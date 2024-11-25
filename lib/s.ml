open Base

let ( @@@ ) f x =
  f x;
  x

module type S0 = sig
  type t

  val zero : t
  val one : t
  val add : t -> t -> t
  val mul : t -> t -> t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val pp : t Fmt.t
end

module MakeSyntax (R : S0) = struct
  include R

  module DSL = struct
    let ( + ) = R.add
    let ( * ) = R.mul
  end
end

module type S = sig
  include S0

  module DSL : sig
    val ( + ) : t -> t -> t
    val ( * ) : t -> t -> t
  end
end

module type CLOSED = sig
  include S

  val star : t -> t
end

module SBool = struct
  module T = struct
    include Bool

    let zero = false
    let one = true
    let add = ( || )
    let mul = ( && )
  end

  include MakeSyntax (T)
end

module MinPlus = struct
  module T = struct
    include Int

    let add = min
    let mul = ( + )
  end

  include MakeSyntax (T)
end

module Free (G : sig
  type t

  val equal : t -> t -> bool
  val compare : t -> t -> int
  val pp : t Fmt.t
end) =
struct
  module T = struct
    type t = Zero | One | Gen of G.t | Add of t * t | Mul of t * t | Star of t
    [@@deriving equal, compare]

    let zero = Zero
    let one = One
    let of_g g = Gen g
    let add x y = match (x, y) with Zero, a | a, Zero -> a | _ -> Add (x, y)

    let mul x y =
      match (x, y) with
      | Zero, _ | _, Zero -> Zero
      | One, a | a, One -> a
      | _ -> Mul (x, y)

    let star x = match x with Zero -> One | One -> One | _ -> Star x

    let rec pp : t Fmt.t =
     fun ppf -> function
      | Zero -> Fmt.string ppf "0"
      | One -> Fmt.string ppf "1"
      | Gen g -> G.pp ppf g
      | Add (x, y) -> Fmt.pf ppf "@[<hov 2>(%a + %a)@]" pp x pp y
      | Mul (x, y) -> Fmt.pf ppf "@[<hov 2>(%a ⋅ %a)@]" pp x pp y
      | Star x -> Fmt.pf ppf "@[<hov 2>%a^*@]" pp x
  end

  include T

  module DSL = struct
    let ( + ) = add
    let ( * ) = mul
    let eps = one
    let null = zero
    let ( ! ) x = of_g x
    let alt = function [] -> null | xs -> List.reduce_exn ~f:add xs
    let seq = function [] -> eps | xs -> List.reduce_exn ~f:mul xs
  end
end

module Regex = struct
  include Free (Char)
end

module SMatrix (R : S) = struct
  module M = Matrix

  let of_view = M.into
  let view = M.out

  module T = struct
    type t = R.t M.t [@@deriving equal, compare]

    let pp : t Fmt.t = M.pp R.pp

    let rec add (m1 : t) (m2 : t) : t =
      (* Logs.debug (fun msg -> msg "%a + %a" pp m1 pp m2); *)
      (fun r -> Logs.debug (fun msg -> msg "%a + %a = %a" pp m1 pp m2 pp r))
      @@@
      let open R.DSL in
      match (m1, m2) with
      | Scalar s1, Scalar s2 -> Scalar (s1 + s2)
      | Matrix m1, Matrix m2 -> Matrix (Matrix.map2_exn ~f:( + ) m1 m2)
      | Scalar s, Matrix m -> add (Matrix m) (Scalar s)
      | Matrix [ [ x ] ], Scalar y -> Matrix [ [ x + y ] ]
      | m, s ->
          let first, top, left, rest = M.out m in
          Matrix.into (add first s, top, left, add rest s)

    let zero = Matrix.Scalar R.zero
    let one = Matrix.Scalar R.one

    let mul (m1 : t) (m2 : t) : t =
      (* Logs.debug (fun msg -> msg "%a * %a" pp m1 pp m2); *)
      (fun r -> Logs.debug (fun msg -> msg "%a * %a = %a" pp m1 pp m2 pp r))
      @@@
      let open R.DSL in
      match (m1, m2) with
      | Scalar a, Scalar b -> Scalar (a + b)
      | Scalar a, Matrix b -> Matrix (M.map b ~f:(fun y -> a * y))
      | Matrix a, Scalar b -> Matrix (M.map a ~f:(fun x -> x * b))
      | Matrix a, Matrix b ->
          Matrix
            (List.map a ~f:(fun row ->
                 List.map (List.transpose_exn b) ~f:(fun col ->
                     List.reduce_exn ~f:( + ) (List.map2_exn row col ~f:( * )))))
  end

  include MakeSyntax (T)
end

module CSMatrix (R : CLOSED) = struct
  include SMatrix (R)

  let rec star (m : t) : t =
    (fun r -> Logs.debug (fun msg -> msg "star %a = %a" pp m pp r))
    @@@
    match m with
    | Scalar s -> Scalar (R.star s)
    | Matrix [ [ s ] ] -> Matrix [ [ R.star s ] ]
    | m ->
        let open DSL in
        let a, b, c, d = M.out m in
        (* Logs.debug (fun msg -> msg "a = %a" pp a);
           Logs.debug (fun msg -> msg "b = %a" pp b);
           Logs.debug (fun msg -> msg "c = %a" pp c);
           Logs.debug (fun msg -> msg "d = %a" pp d); *)
        let a' = star a in
        let b' = a' * b in
        let c' = c * a' in
        let d' = star (d + (c' * a' * b)) in
        (* Logs.debug (fun msg -> msg "star %a = %a" pp a pp a');
           Logs.debug (fun msg -> msg "(star %a) * %a = %a" pp a pp b pp b');
           Logs.debug (fun msg -> msg "%a * (star %a) = %a" pp c pp a pp c');
           Logs.debug (fun msg ->
               msg "star (%a + %a * %a) = %a" pp d pp c pp b pp d'); *)
        M.into (a' + (b' * d' * c'), b' * d', d' * c', d')

  type vec = R.t list

  let pp_vec = Fmt.(hvbox @@ brackets @@ list ~sep:comma R.pp)

  let solve_linear (m : t) (a : vec) : R.t list =
    (* make a square by repeating columns *)
    let a = List.init (List.length a) ~f:(fun _ -> a) |> List.transpose_exn in
    match mul (star m) (M.Matrix a) with
    | M.Matrix a -> List.map a ~f:List.hd_exn
    | _ -> raise M.Malformed
end

module Test () = struct
  let () =
    Logs.set_reporter (Logs_fmt.reporter ());
    Logs.set_level (Some Logs.Debug)

  module M = CSMatrix (Regex)
  open M

  let m =
    M.Matrix
      Regex.(
        DSL.[ [ zero; !'x'; zero ]; [ !'y'; zero; !'z' ]; [ zero; zero; zero ] ])

  let a = Regex.[ zero; zero; one ]
  let sol = solve_linear m a

  let () =
    Logs.debug (fun msg -> msg "m = %a" pp m);
    Logs.debug (fun msg -> msg "a = %a" pp_vec a);
    Logs.debug (fun msg -> msg "sol = %a" pp_vec sol)
end
