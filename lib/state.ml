open Effect
open Effect.Deep

module type STATE = sig
  type t

  val put : t -> unit
  val get : unit -> t
  val run : (unit -> 'a) -> init:t -> 'a
  val run_state : (unit -> 'a) -> init:t -> 'a * t
end

module Make (S : sig
  type t
end) : STATE with type t = S.t = struct
  type t = S.t
  type _ Effect.t += Get : t Effect.t | Put : t -> unit Effect.t

  let get () = perform Get
  let put v = perform (Put v)

  let run_state f ~(init : t) =
    let s = ref init in
    match_with f ()
      {
        retc = (fun x -> (x, !s));
        effc =
          (fun (type b) (eff : b Effect.t) ->
            match eff with
            | Get -> Some (fun (k : (b, _) continuation) -> continue k !s)
            | Put v ->
                Some
                  (fun (k : (b, _) continuation) ->
                    s := v;
                    continue k ())
            | _ -> None);
        exnc = raise;
      }

  let run f ~init = fst (run_state f ~init)
end

(*
module IS = Make (struct
  type t = int
end)

module SS = State (struct
  type t = string
end)
   let foo () : unit =
     assert (0 = IS.get ());
     IS.put 42;
     assert (42 = IS.get ());
     IS.put 21;
     assert (21 = IS.get ());
     SS.put "hello";
     assert ("hello" = SS.get ());
     SS.put "world";
     assert ("world" = SS.get ());
     IS.put 86;
     assert (86 = IS.get ())

   let _ = IS.run (fun () -> SS.run foo ~init:"") ~init:0 *)
