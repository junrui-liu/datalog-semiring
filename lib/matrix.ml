open Base

type 'a t = Scalar of 'a | Matrix of 'a list list [@@deriving equal, compare]

exception Malformed

type 'a view = 'a t * 'a t * 'a t * 'a t

let out : 'a t -> 'a view = function
  | Matrix ((first :: top) :: rows) ->
      let left, rest =
        List.map rows ~f:(fun row -> List.split_n row 1) |> List.unzip
      in
      (Matrix [ [ first ] ], Matrix [ top ], Matrix left, Matrix rest)
  | _ -> raise Malformed

let into : 'a view -> 'a t = function
  | Matrix a, Matrix b, Matrix c, Matrix d ->
      let hcat = List.map2_exn ~f:( @ ) in
      Matrix (hcat a b @ hcat c d)
  | _ -> raise Malformed

let pp : 'a Fmt.t -> 'a t Fmt.t =
  let open Fmt in
  fun ppa ppf -> function
    | Scalar x -> pf ppf "[[%a]]" ppa x
    | Matrix m ->
        (brackets @@ vbox
        @@ list ~sep:(any ";" ++ cut)
        (* @@ brackets  *)
        @@ hbox
        @@ list ~sep:comma ppa)
          ppf m

let map ~f = List.map ~f:(List.map ~f)
let map2_exn ~f = List.map2_exn ~f:(List.map2_exn ~f)
