open Sugartypes

(*
 try { M } as (pat) in { N } otherwise { N' }

  --->

 handle M with {
   Return pat -> N
   _SessionFail _ _ -> N'
 }

*)


module TyEnv = Env.String

let failure_op_name = Value.session_exception_operation

let dp = Sugartypes.dummy_position
let mk_var_pat name : pattern = with_dummy_pos (`Variable (make_binder name `Not_typed dp))
let dummy_pat () = mk_var_pat @@ Utility.gensym ~prefix:"dsh" ()

class insert_toplevel_handlers env =
object (o: 'self_type)
  inherit (TransformSugar.transform env) as super

  method! phrasenode = function
    | (`Spawn (`Wait, _, _, _)) as sw ->
        super#phrasenode sw
    | `Spawn (k, spawn_loc, {node=body; pos=body_loc}, Some inner_effects) ->
        let as_var = Utility.gensym ~prefix:"spawn_aspat" () in
        let as_pat = mk_var_pat as_var in
        let unit_phr = with_dummy_pos (`RecordLit ([], None)) in

        let (o, spawn_loc) = o#given_spawn_location spawn_loc in
        let envs = o#backup_envs in
        let (o, inner_effects) = o#row inner_effects in
        let process_type = `Application (Types.process, [`Row inner_effects]) in
        let o = o#with_effects inner_effects in
        let (o, body, _) = o#phrasenode body in
        let q = QualifiedName.of_name as_var in
        let body =
          `TryInOtherwise (with_pos body_loc body, as_pat,
                           (with_dummy_pos (`Var q)), unit_phr, (Some (Types.unit_type))) in
        let o = o#restore_envs envs in
        (o, (`Spawn (k, spawn_loc, with_pos body_loc body, Some inner_effects)), process_type)
    | e -> super#phrasenode e
end


class desugar_session_exceptions env =
object (o : 'self_type)
  inherit (TransformSugar.transform env) as super

  method! phrasenode = function
    | `Raise ->
        (o, `DoOperation (failure_op_name, [], Some `Not_typed), `Not_typed)
    | `TryInOtherwise (_, _, _, _, None) -> assert false
    | `TryInOtherwise (try_phr, pat, as_phr, otherwise_phr, (Some dt)) ->
        let (o, try_phr, try_dt) = o#phrase try_phr in
        let envs = o#backup_envs in
        let (o, pat) = o#pattern pat in
        let (o, as_phr, _as_dt) = o#phrase as_phr in
        let o = o#restore_envs envs in
        let (o, otherwise_phr, otherwise_dt) = o#phrase otherwise_phr in
        (* Now, to create a handler... *)

        let return_clause = (pat, as_phr) in
        (* Otherwise clause: Distinguished 'session failure' name. Since
         * we'll never use the continuation (and this is invoked after pattern
         * deanonymisation in desugarHandlers), generate a fresh name for the
         * continuation argument. *)
        let cont_pat = dummy_pat () in

        let otherwise_pat : Sugartypes.pattern =
          with_dummy_pos (`Effect (failure_op_name, [], cont_pat)) in

        let otherwise_clause = (otherwise_pat, otherwise_phr) in

        let value_cases = [return_clause] in
        let effect_cases = [otherwise_clause] in

        (* Manually construct a row with the two hardwired handler cases. *)
        let raw_row =
          Types.make_empty_closed_row ()
            |> Types.row_with ("Return", (`Present try_dt))
            |> Types.row_with (failure_op_name, (`Present (otherwise_dt))) in

        let inner_eff =
            Types.make_empty_closed_row ()
            |> Types.row_with ("wild", `Present Types.unit_type)
            |> Types.row_with (failure_op_name, `Present otherwise_dt)
            |> Types.flatten_row
        in

        (* Dummy types *)
        let types =
          (inner_eff, try_dt,
           Types.make_empty_closed_row (), otherwise_dt) in

        let hndl_desc = {
          shd_depth = `Deep;
          shd_types = types;
          shd_raw_row = raw_row;
          shd_params = None;
        } in

        let hndlr = {
          sh_expr = try_phr;
          sh_effect_cases = effect_cases;
          sh_value_cases = value_cases;
          sh_descr = hndl_desc
        } in (o, `Handle hndlr, dt)
    | e -> super#phrasenode e
end


let contains_session_exceptions prog =
  let o =
    object
      inherit SugarTraversals.predicate as super
      val has_exceptions = false
      method satisfied = has_exceptions

      method! phrasenode = function
        | `TryInOtherwise _
        | `Raise -> {< has_exceptions = true >}
        | p -> super#phrasenode p
    end in
  (o#program prog)#satisfied


(*
 * The "naive" typing rule for try-in-otherwise is unsound
 * as it allows possibly-linear variables to be used twice:
 *
 *
 *   G1 |- L : A   G2, x : A |- M : B    G2 |- N : B
 *   -------------------------------------------------
 *      G1, G2 |- try L as x in M otherwise N : B
 *
 * Instead, the typechecker implements a more restrictive typing
 * rule which only allows a single variable in the typing of the
 * success continuation:
 *
 *   G |- L : A   x : A |- M : B     |- N : B
 *   ------------------------------------------
 *     G |- try L as x in M otherwise N : B
 *
 * Thankfully, the full power of the first rule can be restored
 * through the use of a simple macro-translation, performed by the
 * wrap_linear_handlers function:
 *
 * try L as x in M otherwise N
 *   -->
 * switch (try L as x in Just(x) otherwise Nothing) {
 *   case Just(x) -> M
 *   case Nothing -> N
 * }
 *)
let wrap_linear_handlers prog =
  let o =
    object
      inherit SugarTraversals.map as super
      method! phrase = function
        | {node=`TryInOtherwise (l, x, m, n, dtopt); pos} ->
            let fresh_var = Utility.gensym ?prefix:(Some "try_x") () in
            let fresh_pat = with_pos pos (`Variable (make_untyped_binder (with_pos pos fresh_var))) in
            with_pos pos
            (`Switch (
              with_pos pos
               (`TryInOtherwise
                (super#phrase l,
                 fresh_pat,
                 with_pos pos (`ConstructorLit ("Just", Some (with_pos pos (`Var fresh_var)), None)),
                 with_pos pos (`ConstructorLit ("Nothing", None, None)), dtopt)),
              [
                (with_pos pos (`Variant ("Just", (Some x))), super#phrase m);
                (with_pos pos (`Variant ("Nothing", None)), super#phrase n)
              ], None))
        | p -> super#phrase p
    end
  in o#program prog

let settings_check prog =
  if not (contains_session_exceptions prog) then () else
  if not (Settings.get_value Basicsettings.Sessions.exceptions_enabled) then
    failwith ("File contains session exceptions but session_exceptions not enabled. " ^
              "Please set 'session_exceptions' configuration flag to true.")
  else if not (Settings.get_value Basicsettings.Handlers.enabled) then
    failwith ("File contains session exceptions, which require handlers, " ^
              " but handlers are not enabled. " ^
              "Please set 'enable_handlers' configuration flag to true.")
  else ()

let insert_toplevel_handlers env =
  ((new insert_toplevel_handlers env) :
    insert_toplevel_handlers :> TransformSugar.transform)

let desugar_session_exceptions env =
  ((new desugar_session_exceptions env) :
    desugar_session_exceptions :> TransformSugar.transform)

let show prog =
  Printf.printf "%s\n\n" (Sugartypes.show_program prog);
  prog

