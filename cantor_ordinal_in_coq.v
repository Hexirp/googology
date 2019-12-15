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

(* 順序数表記の項を定義する。 *)

Definition nat_iter {P : Type} (o : P) (s : P -> P) (n : nat) : P
  := @nat_rect (fun _ => P) o (fun _ => s) n.

Definition cantor_ordinal_term : Type := { n & nat_iter Empty_set list n }.

(* 順序数表記の順序を定義する。 *)

Definition order (A : Type) : Type := A -> A -> comparison.

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

Fixpoint cantor_nat_iter_order (n : nat) : order (nat_iter Empty_set list n)
  := match n with
    | O => empty_order
    | S np => lexicographical_order (cantor_nat_iter_order np)
  end.

Definition cantor_ordinal_order : order cantor_ordinal_term
  := fun x y => match x, y with
    | existT _ xn xe, existT _ yn ye => match nat_order xn yn with
      | Eq => cantor_nat_iter_order xyn xe ye
      | Lt => Lt
      | Gt => Gt
      end
    end.
