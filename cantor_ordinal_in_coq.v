(* やあ。 Hexirp だよ。 *)

Require Import Coq.Init.Prelude.

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

Definition relation (A : Type) : Type := A -> A -> Type.

Definition empty_order : relation Empty_set
  := @Empty_set_rect (fun _ => Empty_set -> Type).

Open Scope list_scope.

Definition lexicographical_order (A : Type) (order_A : relation A) : relation (list A)
  := fix order (x : list A) (y : list A) : Type
    := match x, y with
      | nil, nil => Empty_set
      | nil, yv :: ys => unit
      | xv :: xs, nil => Empty_set
      | xv :: xs, yv :: ys => sum (order_A xv yv) (order xs ys)
    end.
