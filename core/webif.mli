(** Web interface *)

open Webserver_types

val realpages : bool Settings.setting

module WebIf : functor (Webs : WEBSERVER) ->
sig

  val should_contain_client_id : (string * string) list -> bool

  val do_request :
    (Value.env * Ir.var Env.String.t * FrontendTypeEnv.t) ->
    (string * string) list ->
    (unit -> (string * string) Lwt.t) ->
    Value.continuation ->
    (Value.t -> string) ->
    ((string * string) list -> string -> 'b Lwt.t) ->
    'b Lwt.t

end
