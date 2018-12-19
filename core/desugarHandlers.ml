open Utility
open Sugartypes

(*

 [open] [shallow]handler(m) {
    case Op_i(p_i,k_i) -> ...
    case Return(x) -> ...
  }
  =>
  fun(m) {
    handle(m) {
      case Op_i(p_i,k_i) -> ...
      case Return(x) -> ...
    }
  }

*)


(* Computes the set of names in a given pattern *)
let rec names : pattern -> string list
  = fun pat ->
    match pat.node with
      `Variant (_,pat_opt) -> opt_app names [] pat_opt
    | `Record (name_pats,pat_opt) ->
       let optns = opt_app names [] pat_opt in
       (List.fold_left (fun ns p -> (names p) @ ns) [] (List.map snd name_pats)) @ optns
    | `Variable bndr              -> [name_of_binder bndr]
    | `Cons (pat,pat')            -> (names pat) @ (names pat')
    | `Tuple pats
    | `List pats                  -> List.fold_left (fun ns pat -> (names pat) @ ns ) [] pats
    | `Negative ns'               -> List.fold_left (fun ns n -> n :: ns) [] ns'
    | `As  (bndr,pat)             -> [name_of_binder bndr] @ (names pat)
    | `HasType (pat,_)            -> names pat
    | _                           -> []

(* This function resolves name conflicts in a given pattern p.
   The conflict resolution is simple:
   Given a set of conflicting names ns, then for every name n if (n \in p && n \in ns) then n gets rewritten as _.
 *)
let resolve_name_conflicts : pattern -> stringset -> pattern
  = fun pat conflicts ->
    let rec hide_names : pattern -> pattern
      = fun pat -> with_pos pat.pos
         begin
          match pat.node with
          | `Variant (label, pat_opt)    -> `Variant (label, opt_map hide_names pat_opt)
          | `Record (name_pats, pat_opt) -> `Record  (List.map (fun (label, pat) -> (label, hide_names pat)) name_pats, opt_map hide_names pat_opt)
          | `Variable bndr               ->
             if StringSet.mem (name_of_binder bndr) conflicts
             then `Any
             else pat.node
          | `Cons (pat, pat')            -> `Cons (hide_names pat, hide_names pat')
          | `Tuple pats                  -> `Tuple (List.map hide_names pats)
          | `List pats                   -> `List (List.map hide_names pats)
          | `Negative _                  -> failwith "desugarHandlers.ml: hide_names `Negative not yet implemented"
          | `As (bndr,pat)               -> let {node;_} as pat = hide_names pat in
                                            if StringSet.mem (name_of_binder bndr) conflicts
                                            then node
                                            else `As (bndr, pat)
          | `HasType (pat, t)            -> `HasType (hide_names pat, t)
          | _ -> pat.node
         end
    in hide_names pat

(* This function parameterises each clause computation, e.g.
 fun(m)(s) {
   handle(m) {
     case Op_i(p,k) -> M
     case Return(x) -> N
   }
 } =>
 fun(m)(s) {
   handle(m) {
     case Op_i(p,k) -> fun(s) { M }
     case Return(x) -> fun(s) { N }
   }
 }
 Furthermore, the function resolves name conflicts between clause-parameters
 and the parameters of the introduced functions which encompass clause bodies. Currently,
 the clause-parameters shadow the introduced function parameters.
*)
let parameterize : (pattern * phrase) list -> pattern list list option -> (pattern * phrase) list
  = fun cases params ->
  let wrap_fun params body =
    with_dummy_pos (`FunLit (None, `Unl, (params, body), `Unknown))
  in
  match params with
    None
  | Some [] -> cases
  | Some params ->
     List.map (fun (pat, body) ->
       let name_conflicts =
         let param_names = List.concat (List.map names (List.concat params)) in
         let pat_names   = names pat in
         StringSet.inter (StringSet.from_list pat_names) (StringSet.from_list param_names)
       in
       let params = List.map (List.map (fun p -> resolve_name_conflicts p name_conflicts)) params in
       (pat, wrap_fun params body)
     ) cases


(* This function assigns fresh names to `Any (_) *)
let rec deanonymize : pattern -> pattern
  = fun pat -> with_pos pat.pos
     begin
      match pat.node with
        `Any                         -> `Variable (make_untyped_binder (with_dummy_pos (Utility.gensym ~prefix:"dsh" ())))
      | `Nil                         -> `Nil
      | `Cons (p, p')                -> `Cons (deanonymize p, deanonymize p')
      | `List ps                     -> `List (List.map deanonymize ps)
      | `Effect (name, ps, kpat)     -> `Effect (name, List.map deanonymize ps, deanonymize kpat)
      | `Variant (name, pat_opt)     -> `Variant (name, opt_map deanonymize pat_opt)
      | `Negative ns                 -> `Negative ns
      | `Record (name_pats, pat_opt) -> `Record (List.map (fun (n,p) -> (n, deanonymize p)) name_pats, opt_map deanonymize pat_opt)
      | `Tuple ps                    -> `Tuple (List.map deanonymize ps)
      | `Constant c                  -> `Constant c
      | `Variable b                  -> `Variable b
      | `As (b,p)                    -> `As (b, deanonymize p)
      | `HasType (p,t)               -> `HasType (deanonymize p, t)
     end

(* This function translates a pattern into a phrase. It assumes that the given pattern has been deanonymised. *)
let rec phrase_of_pattern : pattern -> phrase
  = fun pat -> with_pos pat.pos
     begin
      match pat.node with
        `Any                         -> assert false (* can never happen after the fresh name generation pass *)
      | `Nil                         -> `ListLit ([], None)
      | `Cons (hd, tl)               -> `InfixAppl (([], `Cons), phrase_of_pattern hd, phrase_of_pattern tl) (* x :: xs => (phrase_of_pattern x) :: (phrase_of_pattern xs) *)
      | `List ps                     -> `ListLit (List.map phrase_of_pattern ps, None)
      | `Effect _                    -> assert false
      | `Variant (name, pat_opt)     -> `ConstructorLit (name, opt_map phrase_of_pattern pat_opt, None)
      | `Negative _                 -> failwith "desugarHandlers.ml: phrase_of_pattern case for `Negative not yet implemented!"
      | `Record (name_pats, pat_opt) -> `RecordLit (List.map (fun (n,p) -> (n, phrase_of_pattern p)) name_pats, opt_map phrase_of_pattern pat_opt)
      | `Tuple ps                    -> `TupleLit (List.map phrase_of_pattern ps)
      | `Constant c                  -> `Constant c
      | `Variable b                  -> `Var (name_of_binder b)
      | `As (b,_)                    -> `Var (name_of_binder b)
      | `HasType (p,t)               -> `TypeAnnotation (phrase_of_pattern p, t)
     end

(* This function applies the list of parameters to the generated handle. *)
let apply_params : phrase -> phrase list list -> phrase
  = fun h pss ->
    List.fold_right (fun ps acc -> with_dummy_pos (`FnAppl (acc, ps)) ) (List.rev pss) h

let split_handler_cases : (pattern * phrase) list -> (pattern * phrase) list * (pattern * phrase) list
  = fun cases ->
    let ret, ops =
      List.fold_left
        (fun (val_cases, eff_cases) (pat, body) ->
          match pat.node with
          | `Variant ("Return", None)     -> failwith "Improper pattern-matching on return value"
          | `Variant ("Return", Some pat) -> (pat, body) :: val_cases, eff_cases
          | _                             -> val_cases, (pat, body) :: eff_cases)
        ([], []) cases
    in
    match ret with
    | [] ->
       let x = "x" in
       let xb = make_untyped_binder (with_dummy_pos x) in
       let id = (with_dummy_pos (`Variable xb), (with_dummy_pos (`Var x))) in
       ([id], List.rev ops)
    | _ ->
       (List.rev ret, List.rev ops)

let funlit_of_handlerlit : Sugartypes.handlerlit -> Sugartypes.funlit
  = fun (depth, m, cases, params) ->
    let pos = m.pos in
    let m    = deanonymize m in
    let comp = with_pos pos (`FnAppl (phrase_of_pattern m, [])) in
    let cases = parameterize cases params in
    let hndlr = SugarConstructors.Make.untyped_handler comp cases depth in
    let handle = with_pos pos (`Block ([], (with_pos pos (`Handle hndlr)))) in
    let params = opt_map (List.map (List.map deanonymize)) params in
    let body  =
      match params with
        None -> handle
      | Some params ->
         let params = List.map (List.map phrase_of_pattern) params in
         apply_params handle params
    in
    let fnparams : pattern list list = [[]] in
    let fnparams =
      match params with
        Some params -> params @ ([m] :: fnparams)
      | None -> [m] :: fnparams
    in
    let fnlit = (fnparams, body) in
    fnlit

let desugar_handlers_early =
object
  inherit SugarTraversals.map as super
  method! phrasenode = function
    | `HandlerLit hnlit ->
       let fnlit = funlit_of_handlerlit hnlit in
       let funlit : Sugartypes.phrasenode = `FunLit (None, `Unl, fnlit, `Unknown) in
       super#phrasenode funlit
    | e -> super#phrasenode e

  method! phrase {node; pos} =
    match node with
    | `Handle h ->
       let (val_cases, eff_cases) = split_handler_cases h.sh_effect_cases in
       with_pos pos (`Handle { h with sh_effect_cases = eff_cases;
                                      sh_value_cases  = val_cases })
    | _ -> super#phrase {node; pos}

  method! bindingnode = function
    | `Handler (binder, hnlit, annotation) ->
       let fnlit  = funlit_of_handlerlit hnlit in
       `Fun (binder, `Unl, ([], fnlit), `Unknown, annotation)
    | b -> super#bindingnode b
end
