Declare ML Module "ltac_plugin" .

Global Set Default Proof Mode "Classic" .

Global Set Default Goal Selector "!" .

Global Unset Elimination Schemes .

Global Set Universe Polymorphism .

Global Set Polymorphic Inductive Cumulativity .

Global Set Printing Universes .

Module Part_1 .

Module ゼロ段階のブラウワー順序数 .

Inductive ゼロ段階のブラウワー順序数@{ i | } : Type@{ i } := .

Definition 場合分け@{ i | } : forall 目標 : Type@{ i } , ゼロ段階のブラウワー順序数@{ i } -> 目標
  := fun 目標 : Type@{ i } => fun 対象 : ゼロ段階のブラウワー順序数@{ i } => match 対象 with end
.

End ゼロ段階のブラウワー順序数 .

Definition ゼロ段階のブラウワー順序数@{ i | } : Type@{ i }
  := ゼロ段階のブラウワー順序数.ゼロ段階のブラウワー順序数@{ i }
.

Module 一段階のブラウワー順序数 .

Inductive 一段階のブラウワー順序数@{ i | } : Type@{ i }
  := ゼロ段階の構築子 : ( ゼロ段階のブラウワー順序数@{ i } -> 一段階のブラウワー順序数 ) -> 一段階のブラウワー順序数
.

Definition 場合分け@{ i | }
  :
    forall 目標 : Type@{ i } ,
    ( ( ゼロ段階のブラウワー順序数@{ i } -> 目標 ) -> 目標 )
    ->
    一段階のブラウワー順序数@{ i }
    ->
    目標
  :=
    fun 目標 : Type@{ i } =>
    fun ゼロ段階の構築子の処理 : ( ゼロ段階のブラウワー順序数@{ i } -> 目標 ) -> 目標 =>
    fix a ( 対象 : 一段階のブラウワー順序数@{ i } ) { struct 対象 } : 目標
      :=
        match
          対象
        with
          ゼロ段階の構築子 対象_ゼロ段階の列
          =>
          ゼロ段階の構築子の処理 ( fun 添字 : ゼロ段階のブラウワー順序数@{ i } => a ( 対象_ゼロ段階の列 添字 ) )
        end
.

Definition 簡易版の場合分け@{ i | }
  :
    forall 目標 : Type@{ i } ,
    目標
    ->
    一段階のブラウワー順序数@{ i }
    ->
    目標
  :=
    fun 目標 : Type@{ i } =>
    fun ゼロ段階の構築子の処理 : 目標 =>
    場合分け@{ i }
      目標
      ( fun 対象_ゼロ段階の列 : ゼロ段階のブラウワー順序数@{ i } -> 目標 => ゼロ段階の構築子の処理 )
.

Definition ゼロ@{ i | } : 一段階のブラウワー順序数@{ i }
  := ゼロ段階の構築子@{ i } ( ゼロ段階のブラウワー順序数.場合分け@{ i } 一段階のブラウワー順序数@{ i } )
.

End 一段階のブラウワー順序数 .

End Part_1 .
