(** [ltac_plugin] を読み込む。 *)

Declare ML Module "ltac_plugin" .

(** 対話証明の形式を [Classic] とする。 *)

Global Set Default Proof Mode "Classic" .

(** 目標を選ぶ方法を [!] とする。 *)

Global Set Default Goal Selector "!" .

(** [Elimination Schemes] を無効にする。 *)

Global Unset Elimination Schemes .

(** [Universe Polymorphism] を有効にする。 *)

Global Set Universe Polymorphism .

(** [Polymorphic Inductive Cumulativity] を有効にする。 *)

Global Set Polymorphic Inductive Cumulativity .

(** [Primitive Projections] を有効にする。 *)

Global Set Primitive Projections .

(** 宇宙の詳細を表示するようにする。 *)

Global Set Printing Universes .

(** [forall _ : x, y] の糖衣構文として [x -> y] を定義する。 << https://github.com/coq/coq/blob/aaa8c94362b9159b1fa00baff8cd50cdc2972c7f/theories/Init/Notations.v#L15 >> を参照しています。 *)

Notation "x -> y" := ( forall _ : x , y ) ( at level 99 , right associativity , y at level 200 ) .

(** 空の型を定義する。 *)

Definition 空の型 : Set := forall 目標 : Set , 目標 .

(** 出る。空の型の値がある時には、そのような世界から出ることができる。 *)

Definition 出る ( 目標 : Set ) ( 空の型の値 : 空の型 ) : 目標 := 空の型の値 目標 .

(** 単一の型を定義する。 *)

Definition 単一の型 : Set := forall 目標 : Set , 目標 -> 目標 .

(** 単一の型の値を定義する。 *)

Definition 単一の型の値 : 単一の型 := fun 目標 : Set => fun 処理 : 目標 => 処理 .

(** 自然数の型を定義する。 *)

Definition 自然数の型 : Set := forall 目標 : Set , 目標 -> ( 目標 -> 目標 ) -> 目標 .

(** ゼロを定義する。 *)

Definition ゼロ : 自然数の型
  :=
    fun 目標 : Set =>
    fun ゼロの場合の処理 : 目標 =>
    fun 後者の場合の処理 : 目標 -> 目標 =>
    ゼロの場合の処理
.

(** 後者関数を定義する。 *)

Definition 後者関数 : 自然数の型 -> 自然数の型
  :=
    fun 一番目の自然数 : 自然数の型 =>
    fun 目標 : Set =>
    fun ゼロの場合の処理 : 目標 =>
    fun 後者の場合の処理 : 目標 -> 目標 =>
    後者の場合の処理 ( 一番目の自然数 目標 ゼロの場合の処理 後者の場合の処理 )
.

(** 加算を定義する。 *)

Definition 加算 : 自然数の型 -> 自然数の型 -> 自然数の型
  :=
    fun 一番目の自然数 : 自然数の型 =>
    fun 二番目の自然数 : 自然数の型 =>
    二番目の自然数 自然数の型 一番目の自然数 後者関数
.

(** 道を定義する。 *)

Definition 道 ( 一番目の型 : Set ) ( 一番目の値 : 一番目の型 ) : 一番目の型 -> Set
  :=
    fun 二番目の値 : 一番目の型 =>
    forall 目標 : 一番目の型 -> Set ,
    forall 処理 : 目標 一番目の値 ,
    目標 二番目の値
.

(** 一番目の定理を定義する。 *)

Definition 一番目の定理 ( 一番目の自然数 : 自然数の型 )
  : 道 自然数の型 ( 加算 一番目の自然数 ゼロ ) 一番目の自然数
.
Proof .
  unfold 道 .
  intros 目標 処理 .
  unfold 加算 in 処理 .
  unfold ゼロ in 処理 .
  exact 処理 .
Defined .

(** 二番目の定理を定義する。 *)

Definition 二番目の定理 ( 一番目の自然数 : 自然数の型 ) ( 二番目の自然数 : 自然数の型 )
  :
    道
      自然数の型
      ( 加算 一番目の自然数 ( 後者関数 二番目の自然数 ) )
      ( 後者関数 ( 加算 一番目の自然数 二番目の自然数 ) )
.
Proof .
  unfold 道 .
  intros 目標 処理 .
  unfold 加算 in 処理 .
  unfold 加算 .
  exact 処理 .
Defined .

(** 不可能な例を示す。 *)

Fail Definition 三番目の定理  ( 一番目の自然数 : 自然数の型 )
  : 道 自然数の型 ( 加算 ゼロ 一番目の自然数 ) 一番目の自然数
  := fun 目標 : 自然数の型 -> Set => fun 処理 : 目標 ( 加算 ゼロ 一番目の自然数 ) => 処理
.
