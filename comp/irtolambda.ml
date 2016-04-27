(*pp deriving *)
(* Translation of Links IR into OCaml Lambda IR *)
module L = Lambda	     

(* Hello world in Links
([`Fun ((1790, ((String) ~> (), "myprint", `Global )),
         ([(6429, (`Unl , `Any ), `Row ...)],
           [(1789, (String, "", `Local ))],
           ([`Let ((1788, (String, "s", `Local )),
                    ([], `Return `Variable 1789))],
             `Apply (`TApp (`TAbs ([(6427, (`Unl , `Any ), `Row ...)],
                                    `TApp (`Variable 61,
                                            [`Row ({}, ..., false)])),
                             [`Row ({}, ..., false)]), [`Variable 1788]))),
         None, `Unknown )],
  `Apply (`TApp (`TAbs ([(6431, (`Unl , `Any ), `Row ...)],
                         `TApp (`Variable 1790, [`Row ({}, ..., false)])),
                  [`Row ({}, ..., false)]),
           [`Constant `String "Hello World!"]))

 *)

type binder = int * string
	      deriving (Show)
type var    = binder		
  		deriving (Show)

type binder_map = (int * string) list
		 deriving (Show)
type lwlambda = [
  | `Let of binder * lwlambda * lwlambda
  | `Letrec of (binder * lwlambda) list * lwlambda
  | `Fun of binder list * lwlambda
  | `Constant of Constant.constant
  | `Variable of var
  | `Apply of lwlambda * lwlambda list
  | `Primitive of string
  | `PrimOperation of string * lwlambda list
  | `If of lwlambda * lwlambda * lwlambda
  | `Inject of string * lwlambda option
  | `Project of string * lwlambda
  | `Unit
  | `Record of lwlambda list
  | `Case of lwlambda * (string * (binder * lwlambda)) list * (binder * lwlambda) option 
  | `Wrong (* Escape hatch *)
  ]
  deriving (Show)

module Translate = struct
  (* Builds a map from Var ids to names *)    
  let binders_map prog =    
    let rec computation : (Ir.var * string) list -> Ir.computation -> (Ir.var * string) list =
      fun map (bs, tc) ->
      tail_computation (bindings map bs) tc
    and tail_computation : (Ir.var * string) list -> Ir.tail_computation -> (Ir.var * string) list =
      fun map ->
      function
      | `Case (v, clauses, default_clause) ->
	 let map = Utility.StringMap.fold (fun _ (b,c) map -> computation (binder b :: map) c) clauses map in
	 map @ (Utility.from_option [] (Utility.opt_map (fun (b,c) -> computation (binder b :: map) c) default_clause))
      | `If (v, c1, c2) -> (computation map c2) @ (computation map c2)
      | _ -> map
    and bindings : (Ir.var * string) list -> Ir.binding list -> (Ir.var * string) list  =
      fun map -> 
      function
      | b :: bs ->
	 begin
	   match b with
	   | `Let (b, _)
           | `Alien (b,_) -> bindings ((binder b)::map) bs
           | `Fun (b, (_, args, comp), _, _) ->
	      let map = computation ((binder b :: (List.map binder args)) @ map) comp in
	      bindings map bs
           | `Rec ((b, (_, args, comp), _, _) :: rest) ->	      
	      let funs = List.map (fun f -> `Fun f) rest in
	      let map = computation map comp in
	      let map = bindings (binder b :: (List.map binder args) @ map) funs in
	      bindings map bs
	   | _ -> assert false
	 end
      | [] -> map
    and binder : Ir.binder -> (Ir.var * string) =
      fun b -> (Var.var_of_binder b, Var.name_of_binder b)
    in
    let map = computation [] prog in
    (*Utility.IntMap.from_alist map*) map

  let arith_ops =
    [ "+" 
    ; "-"
    ; "*"
    ; "/"
    ; "^"
    ; "mod"
    ; "+."
    ; "-."
    ; "*."
    ; "/."
    ; "^."
    ]

  (*let string_ops =
  ["^^"] *)
      
  let rel_ops =
    [ "=="
    ; "<>"
    ; "<"
    ; ">"
    ; "<="
    ; ">="
    ]
      
  let is_arithmetic_operation : string -> bool =
    fun op -> List.mem op arith_ops

  let is_relational_operation : string -> bool =
    fun op -> List.mem op rel_ops

  (*let is_string_operation : string -> bool =
  fun op -> List.mem op string_ops*)

  let is_primitive : Var.var -> bool = Lib.is_primitive_var
  let primitive_name : Var.var -> string option
    = fun var ->
    try Some (Lib.primitive_name var) with
    | _ -> None			      

  let rec is_primitive_operation : Ir.value -> string option
    = function
    | `Variable var ->
       begin
	 match primitive_name var with
	 | Some name -> if is_arithmetic_operation name || is_relational_operation name
			then Some name
			else None
	 | None -> None
       end
    | `TAbs (_,v)
    | `TApp (v,_)   -> is_primitive_operation v
    | _ -> None

  type ocaml_function = { module_name : string ; function_name : string }
  let ocaml_function module_name function_name = {module_name = module_name ; function_name = function_name}			
	         	   
  let ocaml_of_links_function f =
    let stdlib = "Pervasives" in
    let listlib = "List" in
    (* Links function, (module name, ocaml function) *)
    List.assoc f
	       [   "print", ocaml_function stdlib "print_endline"
		 ; "intToString", ocaml_function stdlib "string_of_int"
		 ; "floatToString", ocaml_function stdlib "string_of_float"
		 ; "^^", ocaml_function stdlib "^"
		 ; "hd", ocaml_function listlib "hd"
		 ; "tl", ocaml_function listlib "tl"
	       ]
	       
  let compenv modulename function_name =
    (*Compmisc.init_path false;
    Ident.reinit ();*)
    Env.lookup_value
      (Longident.(Ldot (Lident modulename, function_name)))
      Env.empty
      
  let lam_apply f xs = L.Lapply (f, xs, L.no_apply_info)
	     
  let lwlambda_of_ir envs ir =
    let binders_map = binders_map ir in
    let lookup var  =
      try Some (List.assoc var binders_map) with
      | _ -> None
    in (*Utility.IntMap.lookup var binders_map in*)
    let rec computation : Ir.computation -> lwlambda =
      fun (bs,tc) ->
      let lam = bindings bs in
      lam (tail_computation tc)
    and tail_computation : Ir.tail_computation -> lwlambda =
      function
      | `Apply (f, args) ->
	 begin
	   match is_primitive_operation f with
	   | Some fname -> `PrimOperation (fname, List.map value args)
	   | None       -> `Apply (value f, List.map value args)
	 end
      | `If (v, e1, e2) -> `If (value v, computation e1, computation e2)
      | `Case (v, clauses, default) ->
	 let clauses' = Utility.StringMap.to_list (fun k (b,c) -> (k, (binder b, computation c))) clauses in
	 let default' = Utility.opt_map (fun (b,c) -> (binder b, computation c)) default in
	 `Case (value v, clauses', default')
      | `Return v -> value v
      | `Special s -> special s
      | _ -> assert false
    and special : Ir.special -> lwlambda =
      function
      | `Wrong _ -> `Wrong
      | _ -> assert false
    and value : Ir.value -> lwlambda =
      function
      | `Constant c -> `Constant c
      | `Variable var ->
	   if is_primitive var then
	     let (Some name) = primitive_name var in
	     `Primitive name
	   else
	     begin
	       match lookup var with
	       | Some name -> `Variable (var, name)
	       | _  -> let _ = print_endline ("Failed to lookup " ^ (string_of_int var)) in
		       let _ = print_endline (Show_binder_map.show binders_map) in
		       failwith "Lookup"
	     end
      | `TAbs (_,v)
      | `TApp (v,_) -> value v
      | `ApplyPure (f,args) -> tail_computation (`Apply (f,args))
      | `Inject (label, v,_) ->
	 begin
	   match v with
	   | `Extend (vs, None) when Utility.StringMap.size vs == 0 -> `Inject (label, None)
	   | _ -> `Inject (label, Some (value v))
	 end
      | `Project (label, v) -> `Project (label, value v)
      | `Extend (vs, None) when Utility.StringMap.size vs == 0 -> `Unit
      | `Extend (vs, None) ->
	 `Record (Utility.StringMap.to_list (fun _ v -> value v) vs)
      | p -> (print_endline (Ir.Show_value.show p); assert false)   
    and bindings : Ir.binding list -> (lwlambda -> lwlambda) =
      let recursive_funs funs =
	  List.fold_right
	    (fun (b,(_, args, body), _, _) funs ->
	      (binder b, `Fun (List.map binder args, computation body)) :: funs)
	    funs []
      in
      function
      | b :: bs ->
	 (fun k ->
	   begin
	     match b with
	     | `Let (b,(_,comp)) -> `Let (binder b, tail_computation comp, bindings bs k)
	     | `Fun (b, (_, args, body), _, _) -> `Let (binder b, `Fun (List.map binder args, computation body), bindings bs k)
	     | `Rec funs -> `Letrec (recursive_funs funs, bindings bs k)
	     | _ -> assert false
	   end)
      | [] -> fun x -> x
    and binder : Ir.binder -> binder =
      fun b -> (Var.var_of_binder b, Var.name_of_binder b)
    in
    computation ir

  let lambda_of_lwlambda module_name ir =
    let open LambdaDSL in
    let rec translate : lwlambda -> L.lambda =
      function
      | `Constant c -> lconst (constant c)
      | `Variable var -> lvar (ident_of_var var)
      | `Primitive "Nil" -> lconst ff				   
      | `Primitive prim ->
	 let {module_name ; function_name} = ocaml_of_links_function prim in
	 lookup module_name function_name
      | `PrimOperation (op, args) ->	 
	 L.(Lprim (primop op, List.map translate args))
      | `Apply (`Primitive "Cons", args) ->
	 lprim box (List.map translate args)
      | `Apply (f, args) ->
	 let args =
	   if List.length args > 0 then
	     List.map translate args
	   else
	     [lconst unit]
	 in
	 lapply (translate f) args
      | `Letrec (funs, e) ->
	 lletrec (List.map (fun (b,comp) -> (ident_of_binder b, translate comp) ) funs)
		 (translate e)
      | `Let (b, e1, e2) ->
	 llet (ident_of_binder b) (translate e1) (translate e2)
      | `Fun (args, body) ->
	 let args =
	   if List.length args > 0 then
	     List.map ident_of_binder args
	   else
	     [Ident.create (Utility.gensym ())]
	 in
	 lfunction args (translate body)
      | `If (cond, trueb, falseb) ->
	 lif (translate cond) (translate trueb) (translate falseb)
      | `Inject (label, v) ->
	 begin
	   match v with
	   | Some (`Record vs) -> polyvariant label (Some (List.map translate vs))
	   | None -> polyvariant label (Some []) (* FIXME: Nullary variants carry an empty record in order to make pattern-matching easy to implement. *)
	 end
      | `Project (label, v) -> lproject ((int_of_string label)-1) (translate v) (* FIXME: Assuming tuples *)
      | `Unit -> lconst unit
      | `Record vs -> lprim box (List.map translate vs)      
      | `Case (v, clauses, default) ->
	 let v = translate v in
	 let default =
	   match default with
	   | None -> lapply (pervasives "failwith") [lstring "Pattern-matching failed"]
	   | Some (b,c) -> llet (ident_of_binder b) v (translate c)
	 in
	 List.fold_left
	   (fun matchfail (v',(b,c)) ->	     
	     lif (neq (lproject 0 v) (polyvariant v' None)) (* FIXME: assuming we always match on a "box" *)
		 matchfail
		 (llet (ident_of_binder b) (lproject 1 v) (translate c))
	   ) default clauses
      (*      | `Empty -> lprim Pidentity []*)
      | `Wrong -> lapply (pervasives "failwith") [lstring "Fatal error."]
      | _ -> assert false
    and constant : Constant.constant -> L.structured_constant =
      function
      | `String s -> string s
      | `Int i    -> const_base int i
      | `Float f  -> const_base float f
      | `Bool true   -> tt
      | `Bool false  -> ff
      | _ -> assert false
    and primop   : string -> L.primitive =
      fun op ->
      if is_arithmetic_operation op then
	match op with       
	| "+" -> L.Paddint
	| "-" -> L.Psubint
	| "*" -> L.Pmulint
	| "/" -> L.Pdivint
	| "mod" -> L.Pmodint		 
	| "+." -> L.Paddfloat
	| "-." -> L.Psubfloat
	| "*." -> L.Pmulfloat
	| "/." -> L.Pdivfloat
	| _ -> assert false
      else if is_relational_operation op then
	L.Pintcomp (
	    match op with
	    | "==" -> Ceq
	    | "<>" -> Cneq
	    | "<"  -> Clt
	    | ">"  -> Cgt
	    | "<=" -> Cle
	    | ">=" -> Cge
	    | _ -> assert false)
      else assert false
    and ident_of_binder : binder -> Ident.t =
      fun (id,bname) ->
      let bname =
	match bname with
	| "" -> "_v"
	| _ -> bname
      in
      Ident.({ name = bname ; stamp = id ; flags = 0 })
    and ident_of_var : var -> Ident.t = fun var -> ident_of_binder var			      
    in
    Compmisc.init_path false;
    Ident.reinit ();
    (*let id = Ident.( { name = module_name ; flags = 1 ; stamp = 0 } ) in
    L.(Lprim (Psetglobal id, [Lsequence (translate ir, Lprim (Pmakeblock(0, Immutable), []))]))	*)
    (*L.(Lsequence (translate ir, Lprim (Pmakeblock(0, Immutable), [])))*)
    translate ir
end	    
	     
(*class translator env =
object ((o : 'self))
  val env = env

  (*method lookup var = Env_links.Int.find env var*)

  method program : string -> Ir.computation -> L.lambda =
    fun module_name comp ->
    let id = Ident.( { name = module_name ; flags = 1 ; stamp = 0 } ) in
    Lambda.(Lprim (Psetglobal id, [o#computation comp]))
					 
  method computation : Ir.computation -> L.lambda =
    fun (bs,tc) ->
    if List.length bs > 0
    then L.(Lsequence (o#bindings bs, o#tail_computation tc))
    else o#tail_computation tc

  method tail_computation : Ir.tail_computation -> L.lambda =
    function
    | `Apply (f, args) -> lam_apply (o#value f) (List.map o#value args)
    | _ -> assert false

  method special : Ir.special -> L.lambda =
    function
    | _ -> assert false
		  
  method value : Ir.value -> L.lambda =
    function
    | `TApp (v,_)
    | `TAbs (_,v) -> o#value v
    | `Constant c -> L.Lconst (o#constant c)
    | `Variable var ->       
       (* Figure out whether the variable is a primitive *)
       if is_primitive var then
	 let (Some name) = primitive_name var in
	 o#primitive name
       else
	 let name = "_x" ^ (string_of_int var) in
	 let ident = Ident.create_persistent name in
	 L.(Lvar ident)
    | `ApplyPure (f, args) ->
       begin
	 match o#is_primitive_operation f with
	 | Some name -> L.(Lprim (o#primitive_operation name, List.map o#value args))
	 | None -> o#tail_computation (`Apply (f,args))
       end
    | _ -> assert false
		  
  method constant : Constant.constant -> L.structured_constant =
    function
    | `String s -> L.Const_immstring s
    | `Int i    -> L.Const_base (Asttypes.Const_int i)
    | _ -> assert false

  method binder : Ir.binder -> Ident.t =
    fun b ->
    let name = "_x" ^ (string_of_int (Var.var_of_binder b)) in
    Ident.create_persistent name
				 		  
(*  method binding : Ir.binding -> (L.lambda -> L.lambda) =
    function
    | `Fun (b, (_, args, body), _,_) ->
       fun scope ->
       L.(Llet (Strict
	       , o#binder b
	       , Lfunction ({ kind   = Curried
			    ; params = List.map o#binder args
			    ; body   = o#computation body
			   })
	       , scope
	       ))
    | _ -> assert false*)
		  
  method bindings : Ir.binding list -> L.lambda =
    function
    | b :: bs -> assert false
    | _ -> assert false
(*    | bs -> let lam = List.fold_left (fun lam b -> (o#binding b) lam) (fun x -> x) bs in
	    lam L.(Lconst (L.Const_base (Asttypes.Const_int 0)))
    | [] -> failwith "Empty list of bindings"*)
		  
  method primitive : string -> L.lambda =
    fun prim ->
    let {module_name ; function_name} = ocaml_of_links_function prim in
    L.(transl_path ~loc:Location.none Env.empty (fst (compenv module_name function_name)))

  method primitive_operation : string -> L.primitive =
    function     
    | "+" -> L.Paddint
    | _ -> assert false
     
  method is_primitive_operation : Ir.value -> string option
    = function
    | `Variable var ->
       begin
	 match primitive_name var with
	 | Some name -> if is_arithmetic_operation name || is_relational_operation name
			then Some name
			else None
	 | None -> None
       end
    | `TApp (v,_)   -> o#is_primitive_operation v
    | _ -> None
end

let invert env =
  let module Env = Env_links in
  Env.String.fold
    (fun name var env ->
      if Env.Int.has env var then
        failwith ("(invert_env) duplicate variable in environment")
      else
        Env.Int.bind env (var, name))
    env Env.Int.empty	   *)

			    
let lambda_of_ir envs prog =
  let lwlam = Translate.lwlambda_of_ir envs prog in
  Translate.lambda_of_lwlambda "test" lwlam
(*  let ir_translator = new translator (invert env) in
  ir_translator#program "Helloworld" prog*)