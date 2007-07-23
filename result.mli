(*pp deriving *)
(** Defines the "values" of Links, and ops on them, including continuations *)

exception Runtime_error of string
exception UnrealizableContinuation

class type otherfield
 = object method show : string end

type db_field_type =
    BoolField
  | TextField
  | IntField
  | FloatField
  | SpecialField of otherfield

type db_status = QueryOk | QueryError of string

class virtual dbresult :
  object
    method virtual error : string
    method virtual fname : int -> string
    method virtual ftype : int -> db_field_type
    method virtual get_all_lst : string list list
    method virtual nfields : int
    method virtual status : db_status
  end

class virtual database :
  object
    method virtual driver_name : unit -> string
    method virtual equal_types : Types.datatype -> db_field_type -> bool
    method virtual escape_string : string -> string
    method virtual exec : string -> dbresult
    method make_insert_query : (string * string list * string list list) -> string
  end

type db_constructor = string -> database * string

val register_driver : string * db_constructor -> unit
val db_connect : string -> string -> database * string
val parse_db_string : string -> string * string
val reconstruct_db_string : string * string -> string


(** Values and continuations for the interpreter **)
type unop = | MkColl
            | MkVariant of string
            | Abs
            | MkDatabase
            | VrntSelect of
                (string * string * Syntax.expression * string option *
                   Syntax.expression option)
            | Erase of string
            | Project of string
            | QueryOp of (Query.query * (* the table aliases: *) string list)
type binop = 
    [ Syntax.comparison
    | `Union
    | `App
    | `RecExt of string
    | `MkTableHandle of Types.row]
type xmlitem =
    | Text of string 
    | Attr of (string * string) 
    | Node of (string * xml)
and xml = xmlitem list
type table = (database * string) * string * Types.row
type primitive_value =
    [ `Bool of bool
    | `Char of char
    | `Database of (database * string)
    | `Table of table
    | `Float of float
    | `Int of Num.num
    | `XML of xmlitem 
    | `NativeString of string
    ]
type result = [ primitive_value
| `Continuation of continuation
| `RecFunction of ((string * Syntax.expression) list * environment * string)
| `PrimitiveFunction of string
| `ClientFunction of string
| `List of result list
| `Record of (string * result) list
| `Abs of result
| `Variant of string * result ]
and contin_frame =
    | Definition of (environment * string)
    | FuncEvalCont of (Syntax.expression list * environment)
    | ArgEvalCont of (environment * result *Syntax.expression list * result list)
    | ApplyCont of (environment * result list)
    | LetCont of (environment * string * Syntax.expression)
    | BranchCont of (environment * Syntax.expression * Syntax.expression)
    | BinopRight of (environment * binop * Syntax.expression)
    | BinopApply of (environment * binop * result)
    | UnopApply of (environment * unop)
    | RecSelect of (environment * string * string * string * Syntax.expression)
    | CollExtn of
        (environment * string * Syntax.expression * result list list *
           result list)
    | StartCollExtn of (environment * string * Syntax.expression)
    | XMLCont of
        (environment * string * string option * xml *
           (string * Syntax.expression) list * Syntax.expression list)
    | Ignore of (environment * Syntax.expression)
    | IgnoreDef of (environment * Syntax.definition)
    | Recv 
and continuation = contin_frame list
and binding = string * result
and environment = binding list  deriving (Show, Dump)
val toplevel_cont : continuation
val expr_of_prim_val : result -> Syntax.expression option
val prim_val_of_expr : Syntax.expression -> result option
val xmlitem_of : result -> xmlitem
val bool : 'a -> [> `Bool of 'a ]
val int : 'a -> [> `Int of 'a ]
val float : 'a -> [> `Float of 'a ]
val char : 'a -> [> `Char of 'a ]
val listval : 'a -> [> `List of 'a ]
val xmlnodeval : string * xml -> [> `XML of xmlitem ]
val is_string : result -> bool
val recfields : result -> (string * result) list
val string_as_charlist : string -> result
val links_fst : [> `Record of ('a * 'b) list ] -> 'b
val links_snd : [> `Record of ('a * 'b) list ] -> 'b
val links_project : string -> [> `Record of (string * 'b) list ] -> 'b
val escape : string -> string
(* val delay_expr : environment -> Syntax.expression -> result *)
val charlist_as_string : result -> string
val string_of_result : result -> string
val string_of_cont : continuation -> string
val string_of_environment : binding list -> string
val string_of_primitive : primitive_value -> string
val box_bool : 'a -> [> `Bool of 'a ]
val unbox_bool : result -> bool
val box_int : 'a -> [> `Int of 'a ]
val unbox_int : result -> Num.num
val box_float : 'a -> [> `Float of 'a ]
val unbox_float : result -> float
val box_char : 'a -> [> `Char of 'a ]
val unbox_char : result -> char
val box_xml : 'a -> [> `XML of 'a ]
val unbox_xml : result -> xmlitem
val box_string : string -> result
val unbox_string : result -> string
val box_list : result list -> result
val unbox_list : result -> result list
val box_unit : unit -> result 
val unbox_unit : result -> unit
val retain : Utility.StringSet.t -> (string * 'b) list -> (string * 'b) list

val marshal_continuation : continuation -> string
val marshal_exprenv : (Syntax.expression * environment) -> string
val marshal_value : result -> string
val broken_unmarshal_value : string -> result
val marshal_result : result -> string

val unmarshal_continuation : result list -> Syntax.program -> string -> continuation
val unmarshal_exprenv : result list -> Syntax.program -> string -> (Syntax.expression * environment)
val unmarshal_result : result list -> Syntax.program -> string -> result

val bind : environment -> string -> result -> environment
val empty_env : environment
val trim_env : environment -> environment
