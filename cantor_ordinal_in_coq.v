(* やあ。 Hexirp だよ。 *)

Require Import Coq.Init.Prelude.

Open Scope list_scope.

(* 今日はね Coq で ε_0 の整礎性を証明したいと思う。 *)
(* そうそう、この記事は巨大数の紹介でもある。 *)
(* 巨大数は、大きな数のことだ。巨大数論は大きな数を研究する学問だ。 *)
(* そこでは、順序数や集合論などが「道具」として使われている。 *)
(* 巨大数界隈だけの用語もある。 *)
(* たとえば ε_0 は Cantor ordinal と巨大数界隈では呼ばれることがある。 *)
(* カントール標準形 (Cantor normal form) の限界であるからだ。 *)
(* この名前は ε_0 という名前より幾ばくか味が付いているように感じる。 *)
(* なので、この記事では epsilon_zero とかではなく cantor_ordinal とかを使う。 *)

(* ε_0 の整礎性を証明するための方針はこうだ。 *)

(* 1. ε_0 と同じ順序型を持つ（はずの）順序を定義する。 *)
(* 2. それが整列順序であることを証明する。 *)

(* それでは始めよう。 *)

Definition eq_rect_nop
  {A : Type} (P : A -> A -> Type)
  (f : forall a : A, P a a)
  (x y : A) (e : x = y) : P x y.
Proof.
  elim e.
  exact (f x).
Defined.

Definition order (A : Type) : Type := A -> A -> comparison.

(* 順序数表記の項を定義する。 *)

Definition nat_iter {P : Type} (o : P) (s : P -> P) (n : nat) : P
  := @nat_rect (fun _ => P) o (fun _ => s) n.

Definition cantor_iter (n : nat) : Type := nat_iter Empty_set list n.

Definition cantor_ordinal_term : Type := { n & cantor_iter n }.

(* 順序数表記の順序を定義する。 *)

Definition empty_order : order Empty_set
  := @Empty_set_rect (fun _ => Empty_set -> comparison).

Definition lexicographical_order {A : Type} (order_A : order A) : order (list A)
  := fix f (x : list A) (y : list A) : comparison
    := match x, y with
      | nil, nil => Eq
      | nil, yv :: ys => Lt
      | xv :: xs, nil => Gt
      | xv :: xs, yv :: ys => match order_A xv yv with
        | Eq => f xs ys
        | Lt => Lt
        | Gt => Gt
      end
    end.

Definition nat_order : order nat
  := fix f (x : nat) (y : nat) : comparison
    := match x, y with
      | O, O => Eq
      | O, S yp => Lt
      | S xp, O => Gt
      | S xp, S yp => f xp yp
    end.

Definition eq_reflection_nat_order : forall x y, nat_order x y = Eq -> x = y
  := fix f (x : nat) (y : nat) {struct x} : nat_order x y = Eq -> x = y
    := match x, y with
      | O, O => fun _ => eq_refl
      | O, S yp => fun p => let H : False
        := let discr : comparison -> Prop
          := fun x => match x with
            | Lt => True
            | _ => False
          end
        in
          eq_ind Lt discr I Eq p
      in
        False_ind (0 = S yp) H
      | S xp, O => fun p => let H : False
        := let discr : comparison -> Prop
          := fun x => match x with
            | Gt => True
            | _ => False
          end
        in
          eq_ind Gt discr I Eq p
      in
        False_ind (S xp = 0) H
      | S xp, S yp => fun p => eq_S xp yp (f xp yp p)
    end.

Fixpoint cantor_iter_order (n : nat) : order (cantor_iter n)
  := match n with
    | O => empty_order
    | S np => lexicographical_order (cantor_iter_order np)
  end.

Definition cantor_ordinal_term_order : order cantor_ordinal_term
  := fun x y => match x, y with
    | existT _ xn xe, existT _ yn ye =>
      let matcher : nat_order xn yn = nat_order xn yn -> comparison :=
        match nat_order xn yn
          as c
          return nat_order xn yn = c -> comparison
        with
          | Eq => fun p =>
            let elimer : nat -> nat -> Type
              := fun x y => cantor_iter x -> cantor_iter y -> comparison
            in
              eq_rect_nop
                (fun x y => elimer x y)
                (fun z xs ys => cantor_iter_order z xs ys)
                xn
                yn
                (eq_reflection_nat_order xn yn p)
                xe
                ye
          | Lt => fun _ => Lt
          | Gt => fun _ => Gt
        end
      in
        matcher eq_refl
  end.

(* 順序数表記の標準形の判定を定義する。 *)

Fixpoint all {A : Type} (p : A -> bool) (x : list A) : bool
  := match x with
    | nil => true
    | xv :: xs => p xv && all p xs
  end.

Fixpoint is_upper_bound_of {A : Type} (order_A : order A) (a : A) (x : list A) : bool
  := let pred : A -> bool
    := fun x => match order_A a x with
      | Eq => true
      | Lt => false
      | Gt => true
    end
  in
    all pred x.

Fixpoint is_sorted {A : Type} (order_A : order A) (x : list A) : bool
  := match x with
    | nil => true
    | xv :: xs => is_upper_bound_of order_A xv xs && is_sorted order_A xs
  end.

Fixpoint cantor_iter_sorted (n : nat) (x : cantor_iter n) : bool
  := let matcher : cantor_iter n -> bool
    := match n with
      | O => fun x => true
      | S np => fun x =>
        (all (cantor_iter_sorted np) x && is_sorted (cantor_iter_order np) x)%bool
    end
  in
    matcher x.

Fixpoint cantor_iter_depth (n : nat) (x : cantor_iter n) : nat
  := let matcher : cantor_iter n -> nat
    := match n with
      | O => fun _ => O
      | S np => fun x => let search_maximum : list (cantor_iter np) -> nat
        := fix f (x : list (cantor_iter np)) : nat
          := match x with
            | nil => 1
            | xv :: xs => max (1 + cantor_iter_depth np xv) (f xs)
          end
      in
        search_maximum x
    end
  in
    matcher x.

Definition cantor_iter_filled (n : nat) (x : cantor_iter n) : bool
  := match nat_order n (cantor_iter_depth n x) with
    | Eq => true
    | Lt => false (* impossible *)
    | Gt => false
  end.

Definition cantor_iter_standard (n : nat) (x : cantor_iter n) : bool
  := cantor_iter_sorted n x && cantor_iter_filled n x.

Definition cantor_ordinal_standard (x : cantor_ordinal_term) : bool
  := match x with
    | existT _ xn xp => cantor_iter_standard xn xp
  end.

(* 順序数表記の本体を定義する。 *)

Definition cantor_ordinal : Type
  := { x : cantor_ordinal_term & cantor_ordinal_standard x = true }.

Definition cantor_ordinal_order : order cantor_ordinal
  := fun x y => match x, y with
    | existT _ xv xe, existT _ yv ye => cantor_ordinal_term_order xv yv
  end.

Definition cantor_ordinal_rel : cantor_ordinal -> cantor_ordinal -> Type
  := fun x y => cantor_ordinal_order x y = Lt.

(* 後は…… cantor_ordinal_rel の三分律と整礎性を証明するだけだ。 *)

(* 整礎性を証明するために階層を作る。 *)

Definition p_cantor_ordinal (n : nat) : Type
  := { x : cantor_iter n & cantor_iter_standard n x = true }.

Definition p_cantor_ordinal_order (n : nat) : order (p_cantor_ordinal n)
  := fun x y => match x, y with
    | existT _ xv xe, existT _ yv ye => cantor_iter_order n xv yv
  end.

Definition p_cantor_ordinal_rel (n : nat) : p_cantor_ordinal n -> p_cantor_ordinal n -> Type
  := fun x y => p_cantor_ordinal_order n x y = Lt.

Definition pp_cantor_ordinal (n : nat) : Type
  := { x : cantor_iter n & cantor_iter_sorted n x = true }.

Definition pp_cantor_ordinal_order (n : nat) : order (pp_cantor_ordinal n)
  := fun x y => match x, y with
    | existT _ xv xe, existT _ yv ye => cantor_iter_order n xv yv
  end.

Definition pp_cantor_ordinal_rel (n : nat)
  : pp_cantor_ordinal n -> pp_cantor_ordinal n -> Type
  := fun x y => pp_cantor_ordinal_order n x y = Lt.

(* 三分律を証明する。 *)

Definition Trichotomy (A : Type) (R : A -> A -> Type) : Type
  := forall x y, sum (x = y) (sum (R x y) (R y x)).

Definition ReflectionOrder
  (A : Type)
  (R : A -> A -> Type)
  (order_A : A -> A -> comparison)
  : Type
  := forall x y, match order_A x y return Type with
    | Eq => x = y
    | Lt => R x y
    | Gt => R y x
  end.

Definition RO_to_Tri
  (A : Type)
  (R : A -> A -> Type)
  (order_A : A -> A -> comparison)
  : ReflectionOrder A R order_A -> Trichotomy A R
  := fun (H : ReflectionOrder A R order_A) => fun x y =>
    let macher : order_A x y = order_A x y -> forall x y, sum (x = y) (sum (R x y) (R y x))
      := match order_A x y as c return order_A x y = c
