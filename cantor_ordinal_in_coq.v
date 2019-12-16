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

Definition eq_reflection_nat_order : forall x y, nat_order x y = Eq -> x = y.
Proof.
  refine (fix f (x : nat) (y : nat) {struct x} : nat_order x y = Eq -> x = y := _).
  refine (match x, y with
    | O, O => _
    | O, S yp => _
    | S xp, O => _
    | S xp, S yp => _
  end).
  - refine (fun _ => eq_refl).
  - refine (fun p => _).
    change (Lt = Eq) in p.
    discriminate.
  - refine (fun p => _).
    change (Gt = Eq) in p.
    discriminate.
  - refine (fun p => _).
    change (nat_order xp yp = Eq) in p.
    apply eq_S.
    apply f.
    exact p.
Defined.

Fixpoint cantor_iter_order (n : nat) : order (cantor_iter n)
  := match n with
    | O => empty_order
    | S np => lexicographical_order (cantor_iter_order np)
  end.

Definition cantor_ordinal_order : order cantor_ordinal_term
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
        := (fix f (x : list (cantor_iter np)) : nat
          := match x with
            | nil => 1
            | xv :: xs => max (cantor_iter_depth np xv) (f xs)
          end)
      in
        search_maximum x
    end
  in
    matcher x.

Definition cantor_ordinal_standard (x : cantor_ordinal_term) : bool
  := match x with
    | existT _ xn xp => cantor_iter_standard xn xp
  end.
