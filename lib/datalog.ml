open Base

let ( @@@ ) f x =
  f x;
  x

module Const = struct
  include String

  let pp = Fmt.string
end

module Pred = struct
  include String

  let pp = Fmt.string
end

module Key = struct
  module T = struct
    type t = Const.t list [@@deriving equal, compare, sexp]
  end

  include T
  include Comparable.Make (T)
end

module Make (Value : S.S) = struct
  module Relation = struct
    type t = { arity : int; table : Value.t Map.M(Key).t }
    [@@deriving equal, compare]

    let pp : t Fmt.t =
      let open Fmt in
      let pp_item ppf (k, v) =
        pf ppf "@[%a = %a@]" (parens (list ~sep:comma string)) k Value.pp v
      in
      using
        (fun { table; _ } -> Map.to_alist table)
        (vbox @@ list @@ hbox @@ pp_item)

    let empty_table = Map.empty (module Key)
    let unit = { arity = 0; table = empty_table }
    let empty arity = { arity; table = empty_table }

    let set { arity; table } ~key ~data =
      assert (List.length key = arity);
      { arity; table = Map.set table ~key ~data }

    let rec pairwise ~equal = function
      | [] | [ _ ] -> true
      | x :: (y :: _ as l) -> equal x y && pairwise ~equal l

    let join ({ arity = a1; table = t1 } : t) ({ arity = a2; table = t2 } : t)
        ~(eqs : int list list) : t =
      {
        arity = a1 + a2;
        table =
          Map.fold t1 ~init:empty_table ~f:(fun ~key:k1 ~data:d1 res ->
              Map.fold t2 ~init:res ~f:(fun ~key:k2 ~data:d2 res ->
                  if
                    List.for_all eqs ~f:(fun is ->
                        pairwise ~equal:Const.equal
                          (List.map is ~f:(fun i -> List.nth_exn (k1 @ k2) i)))
                  then Map.set res ~key:(k1 @ k2) ~data:(Value.mul d1 d2)
                  else res));
      }

    let union ({ arity = a1; table = t1 } : t) ({ arity = a2; table = t2 } : t)
        : t =
      assert (a1 = a2);
      {
        arity = a1;
        table =
          Map.merge t1 t2 ~f:(fun ~key:_ -> function
            | `Left v | `Right v -> Some v
            | `Both (v1, v2) -> Some (Value.add v1 v2));
      }

    let project ({ arity = a; table = t } : t) (is : int list) : t =
      assert (List.for_all is ~f:(fun i -> i < a));
      assert (
        List.length is
        = List.length (List.dedup_and_sort ~compare:Int.compare is));
      {
        arity = List.length is;
        table =
          Map.map_keys_exn
            (module Key)
            t
            ~f:(fun k -> List.map is ~f:(List.nth_exn k));
      }

    let filter (r : t) (cs : (int * Const.t) list) : t =
      let is = List.map cs ~f:fst in
      assert (List.for_all is ~f:(fun i -> i < r.arity));
      assert (
        List.length is
        = List.length (List.dedup_and_sort ~compare:Int.compare is));
      {
        arity = r.arity;
        table =
          Map.filter_keys r.table ~f:(fun k ->
              List.for_all cs ~f:(fun (i, c) ->
                  Const.equal (List.nth_exn k i) c));
      }
  end

  module Db = struct
    type t = Relation.t Map.M(Pred).t

    let pp_item = Fmt.(pair Pred.pp ~sep:(const string " := ") Relation.pp)
    let pp : t Fmt.t = Fmt.(using Map.to_alist (list ~sep:cut pp_item))
  end

  module Surface = struct
    module Atom = struct
      type arg = C of Const.t | V of string
      type t = { pred : Pred.t; args : arg list }
    end

    module Rule = struct
      type t = { head : Atom.t; body : Atom.t list }
    end

    module Axiom = struct
      type t = { pred : Pred.t; args : Const.t list; value : Value.t }
    end

    module Program = struct
      type t = Axiom.t list * Rule.t list
    end
  end

  module Typing = struct
    (** Extensional or Intensional *)
    module Tension = struct
      type t = Ex | In [@@deriving equal]

      let pp ppf = function
        | Ex -> Fmt.string ppf "ex"
        | In -> Fmt.string ppf "in"
    end

    (** A predicate type is a pair of tension and arity *)
    module Ty = struct
      type t = Tension.t * int [@@deriving equal]
    end

    (** Type environment *)
    module Env = struct
      type t = Ty.t Map.M(Pred).t

      let pp : t Fmt.t =
        let open Fmt in
        let pp_item ppf (p, (t, a)) = pf ppf "%s : %a(%d)" p Tension.pp t a in
        using Map.to_alist (vbox @@ list @@ hbox @@ pp_item)
    end

    let empty = Map.empty (module Pred)

    exception Type_error of string

    let check ((axioms, rules) : Surface.Program.t) : Env.t =
      let add m p t xs =
        let ty = (t, List.length xs) in
        Map.update m p ~f:(function
          | None -> ty
          | Some ty' ->
              if Ty.equal ty ty' then ty
              else raise (Type_error "arity mismatch"))
      in
      let check_arity m p xs =
        match Map.find m p with
        | None -> raise (Type_error "undefined predicate")
        | Some (_, a) ->
            if a = List.length xs then ()
            else raise (Type_error "arity mismatch")
      in
      let m =
        List.fold axioms ~init:empty
          ~f:(fun m Surface.Axiom.{ pred; args; _ } ->
            add m pred Tension.Ex args)
      in
      let m =
        List.fold rules ~init:m ~f:(fun m Surface.Rule.{ head; _ } ->
            add m head.pred Tension.In head.args)
      in
      List.iter rules ~f:(fun Surface.Rule.{ body; _ } ->
          List.iter body ~f:(fun Surface.Atom.{ pred; args } ->
              check_arity m pred args));
      m

    let ex_preds (env : Env.t) : (Pred.t * int) list =
      Map.filter_map env ~f:(fun (t, a) ->
          if Tension.(equal t Ex) then Some a else None)
      |> Map.to_alist

    let in_preds (env : Env.t) : (Pred.t * int) list =
      Map.filter_map env ~f:(fun (t, a) ->
          if Tension.(equal t In) then Some a else None)
      |> Map.to_alist
  end

  module Internal = struct
    module RelAlg = struct
      type cond = int * Const.t
      type eq = int list

      type t =
        | P of Pred.t
        | Filter of t * cond list
        | Project of t * int list
        | Unit  (** relation with zero columns (unit of join) *)
        | Join of t * t * eq list
        | Union of t * t

      let rec pp ppf =
        let open Fmt in
        function
        | P p -> pf ppf "%s" p
        | Filter (r, cs) ->
            pf ppf "@[σ_{%a}(%a)@]"
              (list ~sep:(any " = ") (pair int string))
              cs pp r
        | Project (r, is) ->
            pf ppf "@[π_{%a}(%a)@]" (list ~sep:comma int) is pp r
        | Unit -> string ppf "()"
        | Join (r1, r2, eqs) ->
            pf ppf "@[%a ⨝_{%a} %a@]" pp r1
              (list ~sep:comma (list ~sep:(any "=") int))
              eqs pp r2
        | Union (r1, r2) -> pf ppf "%a ∪ %a" pp r1 pp r2

      let p pred = P pred
      let filter r = function [] -> r | cs -> Filter (r, cs)
      let project r is = Project (r, is)
      let unit = Unit

      let join r1 r2 eqs =
        match (r1, r2) with Unit, r | r, Unit -> r | _ -> Join (r1, r2, eqs)

      let union r1 r2 = Union (r1, r2)

      let unions = function
        | [] -> failwith "empty union"
        | [ t ] -> t
        | rs -> List.reduce_exn ~f:union rs
    end

    type plans = RelAlg.t Map.M(Pred).t
    (** plans for evaluating intensional predicates *)

    let pp_plan = Fmt.(pair Pred.pp ~sep:(const string " :- ") RelAlg.pp)

    let pp_plans : plans Fmt.t =
      Fmt.(using Map.to_alist (list ~sep:cut pp_plan))

    type program = {
      env : Typing.Env.t;  (** type environment *)
      edb : Db.t;  (** extensional database *)
      plans : plans;  (** plans for intensional predicates *)
    }

    let pp_program ppf { env; edb; plans } =
      let open Fmt in
      pf ppf "@[<v>%a@ %a@ %a@]" Typing.Env.pp env Db.pp edb pp_plans plans

    module FreshName = struct
      module Counter = State.Make (Int)

      let next ?(prefix = "_") () =
        let i = Counter.get () in
        Counter.put (i + 1);
        Fmt.str "%s%d" prefix i

      let run f = Counter.run f 0
    end

    (** Synthesize a query plan for a given rule in surface syntax *)
    let plan ({ head; body } : Surface.Rule.t) : RelAlg.t =
      let open RelAlg in
      let consts_ks args =
        let costs = ref [] in
        let ks =
          List.mapi args ~f:(fun i -> function
            | Surface.Atom.C c ->
                costs := !costs @ [ (i, c) ];
                FreshName.next ()
            | V v -> v)
        in
        (!costs, ks)
      in
      let e_body, ks_body =
        List.fold body ~init:(unit, [])
          ~f:(fun (e, ks_e) Surface.Atom.{ pred; args } ->
            let consts, ks = consts_ks args in
            (* list of keys *)
            let ks_join = ks_e @ ks in
            let eqs =
              ks_join
              |> List.mapi ~f:(fun i k -> (k, i))
              |> Map.of_alist_multi (module String)
              |> Map.data
              |> List.filter ~f:(fun l -> List.length l > 1)
            in
            (join e (filter (p pred) consts) eqs, ks_join))
      in
      let consts, ks = consts_ks head.args in
      assert (List.is_empty consts);
      project e_body
        (List.map ks ~f:(fun k ->
             match List.findi ks_body ~f:(fun _ k' -> String.equal k k') with
             | None -> failwith "key not found"
             | Some (i, _) -> i))

    let compile ((axioms, rules) as prog : Surface.Program.t) : program =
      let env = Typing.check prog in
      Logs.debug (fun m -> m "Typing env: %a" Typing.Env.pp env);
      let edb =
        Typing.ex_preds env
        |> List.map ~f:(fun (p, arity) ->
               ( p,
                 axioms
                 |> List.filter ~f:(fun Surface.Axiom.{ pred; _ } ->
                        String.equal pred p)
                 |> List.fold ~init:(Relation.empty arity)
                      ~f:(fun r Surface.Axiom.{ args; value; _ } ->
                        Relation.set r ~key:args ~data:value) ))
        |> Map.of_alist_exn (module Pred)
      in
      Logs.debug (fun m -> m "Extensional DB: %a" Db.pp edb);
      let plans =
        Typing.in_preds env
        |> List.map ~f:(fun (p, _) ->
               let rules =
                 List.filter rules ~f:(fun Surface.Rule.{ head; _ } ->
                     String.equal head.pred p)
               in
               let plans = List.map rules ~f:plan in
               (p, RelAlg.unions plans))
        |> Map.of_alist_exn (module Pred)
      in
      { env; edb; plans }
  end

  module Interpret = struct
    let rec eval (db : Db.t) (r : Internal.RelAlg.t) : Relation.t =
      Logs.debug (fun m -> m "Eval %a" Internal.RelAlg.pp r);
      (fun res ->
        Logs.debug (fun m ->
            m "Eval %a = %a" Internal.RelAlg.pp r Relation.pp res))
      @@@
      match r with
      | P p -> Map.find_exn db p
      | Filter (r, cs) -> Relation.filter (eval db r) cs
      | Project (r, is) -> Relation.project (eval db r) is
      | Unit -> Relation.unit
      | Join (r1, r2, eqs) -> Relation.join ~eqs (eval db r1) (eval db r2)
      | Union (r1, r2) -> Relation.union (eval db r1) (eval db r2)

    let run ({ env; edb; plans } : Internal.program) : Db.t =
      let rec go (db : Db.t) : Db.t =
        Logs.debug (fun m -> m "go DB: %a" Db.pp db);
        let delta = ref false in
        let db' =
          Map.fold plans ~init:db ~f:(fun ~key:p ~data:plan db ->
              let r0 = Map.find_exn db p in
              let r = eval db plan in
              if not (Relation.equal r0 r) then (
                delta := true;
                Logs.debug (fun m -> m "Update %s to be %a" p Relation.pp r);
                Map.set db ~key:p ~data:r)
              else (
                Logs.debug (fun m -> m "No update %s" p);
                db))
        in
        if !delta then go db' else db'
      in
      Logs.debug (fun m -> m "Initial DB: %a" Db.pp edb);
      let db =
        List.fold (Typing.in_preds env) ~init:edb ~f:(fun db (p, arity) ->
            Map.set db ~key:p ~data:(Relation.empty arity))
      in
      go db
  end
end

module Test = struct
  let () = Logs.set_reporter (Logs_fmt.reporter ())
  let () = Logs.set_level (Some Logs.Debug)

  module TestBool = struct
    module D = Make (S.SBool)
    open D

    let prog =
      Surface.
        ( Axiom.
            [
              { pred = "E"; args = [ "1"; "2" ]; value = true };
              { pred = "E"; args = [ "2"; "3" ]; value = true };
              { pred = "E"; args = [ "4"; "4" ]; value = true };
              { pred = "E"; args = [ "4"; "3" ]; value = true };
            ],
          Rule.
            [
              {
                head = { pred = "P"; args = [ V "x"; V "y" ] };
                body = [ { pred = "E"; args = [ V "x"; V "y" ] } ];
              };
              {
                head = { pred = "P"; args = [ V "x"; V "z" ] };
                body =
                  [
                    { pred = "E"; args = [ V "x"; V "y" ] };
                    { pred = "P"; args = [ V "y"; V "z" ] };
                  ];
              };
            ] )

    let prog' = Internal.compile prog
    let () = Logs.debug (fun m -> m "%a" Internal.pp_program prog')
    let db = Interpret.run prog'
    let () = Logs.debug (fun m -> m "DB: %a" Db.pp db)
  end

  module TestRegex = struct
    module D = Make (S.Regex)
    open D
  end
end
