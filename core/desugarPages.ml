open Sugartypes

let rec is_raw phrase =
  match phrase.node with
    | `TextNode _ -> true
    | `Block _ -> true
    | `FormletPlacement _
    | `PagePlacement _ -> false
    | `Xml (_, _, _, children) ->
        List.for_all is_raw children
    | _e ->
        raise (Errors.SugarError (phrase.pos, "Invalid element in page literal"))

(* DODGEYNESS:

   The first argument to desugar_page is an object which is only used
   to lookup effecs and to construct formlet types.

   This code assumes that:

     - the effecs are the same throughout the page literal
     - the environment is unchanged after calling o#phrase formlet
*)
let rec desugar_page (o, page_type) =
  let desugar_nodes pos : phrase list -> phrase =
    fun children ->
      let q = QualifiedName.of_name "joinManyP" in
      with_pos pos (`FnAppl (with_pos pos (`TAppl (with_pos pos (`Var q), [`Row (o#lookup_effects)])),
                            [with_pos pos (`ListLit (List.map (desugar_page (o, page_type)) children, Some page_type))]))
  in
    fun ({node=e; pos} as phrase) ->
      match e with
        | _ when is_raw phrase ->
          let q = QualifiedName.of_name "bodyP" in
          (* TODO: check that e doesn't contain any formletplacements or page placements *)
           with_pos pos (`FnAppl (with_pos pos (`TAppl (with_pos pos (`Var q), [`Row (o#lookup_effects)])),
                                 [with_pos pos e]))
        | `FormletPlacement (formlet, handler, attributes) ->
            let (_, formlet, formlet_type) = o#phrase formlet in
            let formlet_type = Types.concrete_type formlet_type in
            let a = Types.fresh_type_variable (`Any, `Any) in
            let b = Types.fresh_type_variable (`Any, `Any) in
            let q = QualifiedName.of_name "formP" in
            let _template = `Alias (("Formlet", [`Type a]), b) in
              Unify.datatypes (`Alias (("Formlet", [`Type a]), b), formlet_type);
              with_pos pos (`FnAppl (with_pos pos (`TAppl (with_pos pos (`Var q), [`Type a; `Row (o#lookup_effects)])),
                                    [formlet; handler; attributes]))
        | `PagePlacement (page) -> page
        | `Xml ("#", [], _, children) ->
            desugar_nodes pos children
        | `Xml (name, attrs, dynattrs, children) ->
            let q = QualifiedName.of_name "plugP" in
            let x = Utility.gensym ~prefix:"xml" () in
            let q' = QualifiedName.of_name x in
              with_pos pos (`FnAppl
              (with_pos pos (`TAppl (with_pos pos (`Var q), [`Row (o#lookup_effects)])),
               [with_pos pos (`FunLit
                           (Some ([Types.make_tuple_type [Types.xml_type], o#lookup_effects]),
                            `Unl,
                            ([[with_pos pos (`Variable (make_binder x Types.xml_type pos))]],
                               with_pos pos (`Xml (name, attrs, dynattrs,
                                             [with_pos pos (`Block ([], with_pos pos (`Var q')))]))), `Unknown));
                desugar_nodes pos children]))
        | _ ->
          raise (Errors.SugarError (pos, "Invalid element in page literal"))

and desugar_pages env =
object
  inherit (TransformSugar.transform env) as super

  method! phrasenode = function
    | `Page e ->
        let (o, e, _t) = super#phrase e in
        let page_type = Instantiate.alias "Page" [] env.Types.FrontendTypeEnv.tycon_env in
        let e = desugar_page (o, page_type) e in
          (o, e.node, page_type)
    | e -> super#phrasenode e
end

let is_pageless =
object
  inherit SugarTraversals.predicate as super

  val pageless = true
  method satisfied = pageless

  method! phrasenode = function
    | `Page _ -> {< pageless = false >}
    | e -> super#phrasenode e
end
