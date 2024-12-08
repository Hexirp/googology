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
  : forall 目標 : Type@{ i } , 目標 -> 一段階のブラウワー順序数@{ i } -> 目標
  :=
    fun 目標 : Type@{ i } =>
    fun ゼロ段階の構築子の処理 : 目標 =>
    場合分け@{ i }
      目標
      ( fun 対象_ゼロ段階の列 : ゼロ段階のブラウワー順序数@{ i } -> 目標 => ゼロ段階の構築子の処理 )
.

Definition ゼロ段階のブラウワー順序数を埋め込む@{ i | }
  : ゼロ段階のブラウワー順序数@{ i } -> 一段階のブラウワー順序数@{ i }
  := ゼロ段階のブラウワー順序数.場合分け@{ i } 一段階のブラウワー順序数@{ i }
.

Definition ゼロ@{ i | } : 一段階のブラウワー順序数@{ i }
  := ゼロ段階の構築子@{ i } ( ゼロ段階のブラウワー順序数.場合分け@{ i } 一段階のブラウワー順序数@{ i } )
.

End 一段階のブラウワー順序数 .

Definition 一段階のブラウワー順序数@{ i | } : Type@{ i }
  := 一段階のブラウワー順序数.一段階のブラウワー順序数@{ i }
.

Module 二段階のブラウワー順序数 .

Inductive 二段階のブラウワー順序数@{ i | } : Type@{ i }
  :=
    ゼロ段階の構築子 : ( ゼロ段階のブラウワー順序数@{ i } -> 二段階のブラウワー順序数 ) -> 二段階のブラウワー順序数
    |
    一段階の構築子 : ( 一段階のブラウワー順序数@{ i } -> 二段階のブラウワー順序数 ) -> 二段階のブラウワー順序数
.

Definition 場合分け@{ i | }
  :
    forall 目標 : Type@{ i } ,
    ( ( ゼロ段階のブラウワー順序数@{ i } -> 目標 ) -> 目標 )
    ->
    ( ( 一段階のブラウワー順序数@{ i } -> 目標 ) -> 目標 )
    ->
    二段階のブラウワー順序数@{ i }
    ->
    目標
  :=
    fun 目標 : Type@{ i } =>
    fun ゼロ段階の構築子の処理 : ( ゼロ段階のブラウワー順序数@{ i } -> 目標 ) -> 目標 =>
    fun 一段階の構築子の処理 : ( 一段階のブラウワー順序数@{ i } -> 目標 ) -> 目標 =>
    fix a ( 対象 : 二段階のブラウワー順序数@{ i } ) { struct 対象 } : 目標
      :=
        match
          対象
        with
          ゼロ段階の構築子 対象_ゼロ段階の列
          =>
          ゼロ段階の構築子の処理 ( fun 添字 : ゼロ段階のブラウワー順序数@{ i } => a ( 対象_ゼロ段階の列 添字 ) )
          |
          一段階の構築子 対象_一段階の列
          =>
          一段階の構築子の処理 ( fun 添字 : 一段階のブラウワー順序数@{ i } => a ( 対象_一段階の列 添字 ) )
        end
.

Definition 簡易版の場合分け@{ i | }
  : forall 目標 : Type@{ i } , 目標 -> ( 目標 -> 目標 ) -> 二段階のブラウワー順序数@{ i } -> 目標
  :=
    fun 目標 : Type@{ i } =>
    fun ゼロ段階の構築子の処理 : 目標 =>
    fun 一段階の構築子の処理 : 目標 -> 目標 =>
    場合分け@{ i }
      目標
      ( fun 対象_ゼロ段階の列 : ゼロ段階のブラウワー順序数@{ i } -> 目標 => ゼロ段階の構築子の処理 )
      (
        fun 対象_一段階の列 : 一段階のブラウワー順序数@{ i } -> 目標 =>
        一段階の構築子の処理 ( 対象_一段階の列 一段階のブラウワー順序数.ゼロ@{ i } )
      )
.

Definition ゼロ段階のブラウワー順序数を埋め込む@{ i | }
  : ゼロ段階のブラウワー順序数@{ i } -> 二段階のブラウワー順序数@{ i }
  := ゼロ段階のブラウワー順序数.場合分け@{ i } 二段階のブラウワー順序数@{ i }
.

Definition ゼロ@{ i | } : 二段階のブラウワー順序数@{ i }
  := ゼロ段階の構築子@{ i } ( ゼロ段階のブラウワー順序数.場合分け@{ i } 二段階のブラウワー順序数@{ i } )
.

Definition 一段階のブラウワー順序数を埋め込む@{ i | }
  : 一段階のブラウワー順序数@{ i } -> 二段階のブラウワー順序数@{ i }
  := 一段階のブラウワー順序数.場合分け@{ i } 二段階のブラウワー順序数@{ i } ゼロ段階の構築子@{ i }
.

Definition 後者関数@{ i | } : 二段階のブラウワー順序数@{ i } -> 二段階のブラウワー順序数@{ i }
  :=
    fun x : 二段階のブラウワー順序数@{ i } =>
    一段階の構築子@{ i } ( 一段階のブラウワー順序数.簡易版の場合分け@{ i } 二段階のブラウワー順序数@{ i } x )
.

Definition 加算@{ i | }
  : 二段階のブラウワー順序数@{ i } -> 二段階のブラウワー順序数@{ i } -> 二段階のブラウワー順序数@{ i }
  :=
    fun x : 二段階のブラウワー順序数@{ i } =>
    簡易版の場合分け@{ i } 二段階のブラウワー順序数@{ i } x 後者関数@{ i }
.

Definition 乗算@{ i | }
  : 二段階のブラウワー順序数@{ i } -> 二段階のブラウワー順序数@{ i } -> 二段階のブラウワー順序数@{ i }
  :=
    fun x : 二段階のブラウワー順序数@{ i } =>
    簡易版の場合分け@{ i }
      二段階のブラウワー順序数@{ i }
      ゼロ@{ i }
      ( fun a_前者 : 二段階のブラウワー順序数@{ i } => 加算@{ i } a_前者 x )
.

Definition 冪乗@{ i | }
  : 二段階のブラウワー順序数@{ i } -> 二段階のブラウワー順序数@{ i } -> 二段階のブラウワー順序数@{ i }
  :=
    fun x : 二段階のブラウワー順序数@{ i } =>
    簡易版の場合分け@{ i }
      二段階のブラウワー順序数@{ i }
      ( 後者関数@{ i } ゼロ@{ i } )
      ( fun a_前者 : 二段階のブラウワー順序数@{ i } => 乗算@{ i } a_前者 x )
.

End 二段階のブラウワー順序数 .

Definition 二段階のブラウワー順序数@{ i | } : Type@{ i }
  := 二段階のブラウワー順序数.二段階のブラウワー順序数@{ i }
.

Module 三段階のブラウワー順序数 .

Inductive 三段階のブラウワー順序数@{ i | } : Type@{ i }
  :=
    ゼロ段階の構築子 : ( ゼロ段階のブラウワー順序数@{ i } -> 三段階のブラウワー順序数 ) -> 三段階のブラウワー順序数
    |
    一段階の構築子 : ( 一段階のブラウワー順序数@{ i } -> 三段階のブラウワー順序数 ) -> 三段階のブラウワー順序数
    |
    二段階の構築子 : ( 二段階のブラウワー順序数@{ i } -> 三段階のブラウワー順序数 ) -> 三段階のブラウワー順序数
.

Definition 場合分け@{ i | }
  :
    forall 目標 : Type@{ i } ,
    ( ( ゼロ段階のブラウワー順序数@{ i } -> 目標 ) -> 目標 )
    ->
    ( ( 一段階のブラウワー順序数@{ i } -> 目標 ) -> 目標 )
    ->
    ( ( 二段階のブラウワー順序数@{ i } -> 目標 ) -> 目標 )
    ->
    三段階のブラウワー順序数@{ i }
    ->
    目標
  :=
    fun 目標 : Type@{ i } =>
    fun ゼロ段階の構築子の処理 : ( ゼロ段階のブラウワー順序数@{ i } -> 目標 ) -> 目標 =>
    fun 一段階の構築子の処理 : ( 一段階のブラウワー順序数@{ i } -> 目標 ) -> 目標 =>
    fun 二段階の構築子の処理 : ( 二段階のブラウワー順序数@{ i } -> 目標 ) -> 目標 =>
    fix a ( 対象 : 三段階のブラウワー順序数@{ i } ) { struct 対象 } : 目標
      :=
        match
          対象
        with
          ゼロ段階の構築子 対象_ゼロ段階の列
          =>
          ゼロ段階の構築子の処理 ( fun 添字 : ゼロ段階のブラウワー順序数@{ i } => a ( 対象_ゼロ段階の列 添字 ) )
          |
          一段階の構築子 対象_一段階の列
          =>
          一段階の構築子の処理 ( fun 添字 : 一段階のブラウワー順序数@{ i } => a ( 対象_一段階の列 添字 ) )
          |
          二段階の構築子 対象_二段階の列
          =>
          二段階の構築子の処理 ( fun 添字 : 二段階のブラウワー順序数@{ i } => a ( 対象_二段階の列 添字 ) )
        end
.

Definition 簡易版の場合分け@{ i | }
  :
    forall 目標 : Type@{ i } ,
    目標
    ->
    ( 目標 -> 目標 )
    ->
    ( ( 二段階のブラウワー順序数@{ i } -> 目標 ) -> 目標 )
    ->
    三段階のブラウワー順序数@{ i }
    ->
    目標
  :=
    fun 目標 : Type@{ i } =>
    fun ゼロ段階の構築子の処理 : 目標 =>
    fun 一段階の構築子の処理 : 目標 -> 目標 =>
    fun 二段階の構築子の処理 : ( 二段階のブラウワー順序数@{ i } -> 目標 ) -> 目標 =>
    場合分け@{ i }
      目標
      ( fun 対象_ゼロ段階の列 : ゼロ段階のブラウワー順序数@{ i } -> 目標 => ゼロ段階の構築子の処理 )
      (
        fun 対象_一段階の列 : 一段階のブラウワー順序数@{ i } -> 目標 =>
        一段階の構築子の処理 ( 対象_一段階の列 一段階のブラウワー順序数.ゼロ@{ i } )
      )
      二段階の構築子の処理
.

Definition ゼロ段階のブラウワー順序数を埋め込む@{ i | }
  : ゼロ段階のブラウワー順序数@{ i } -> 三段階のブラウワー順序数@{ i }
  := ゼロ段階のブラウワー順序数.場合分け@{ i } 三段階のブラウワー順序数@{ i }
.

Definition ゼロ@{ i | } : 三段階のブラウワー順序数@{ i }
  := ゼロ段階の構築子@{ i } ( ゼロ段階のブラウワー順序数.場合分け@{ i } 三段階のブラウワー順序数@{ i } )
.

Definition 一段階のブラウワー順序数を埋め込む@{ i | }
  : 一段階のブラウワー順序数@{ i } -> 三段階のブラウワー順序数@{ i }
  := 一段階のブラウワー順序数.場合分け@{ i } 三段階のブラウワー順序数@{ i } ゼロ段階の構築子@{ i }
.

Definition 後者関数@{ i | } : 三段階のブラウワー順序数@{ i } -> 三段階のブラウワー順序数@{ i }
  :=
    fun x : 三段階のブラウワー順序数@{ i } =>
    一段階の構築子@{ i } ( 一段階のブラウワー順序数.簡易版の場合分け@{ i } 三段階のブラウワー順序数@{ i } x )
.

Definition 加算@{ i | }
  : 三段階のブラウワー順序数@{ i } -> 三段階のブラウワー順序数@{ i } -> 三段階のブラウワー順序数@{ i }
  :=
    fun x : 三段階のブラウワー順序数@{ i } =>
    簡易版の場合分け@{ i } 三段階のブラウワー順序数@{ i } x 後者関数@{ i } 二段階の構築子@{ i }
.

Definition 乗算@{ i | }
  : 三段階のブラウワー順序数@{ i } -> 三段階のブラウワー順序数@{ i } -> 三段階のブラウワー順序数@{ i }
  :=
    fun x : 三段階のブラウワー順序数@{ i } =>
    簡易版の場合分け@{ i }
      三段階のブラウワー順序数@{ i }
      ゼロ@{ i }
      ( fun a_前者 : 三段階のブラウワー順序数@{ i } => 加算@{ i } a_前者 x )
      二段階の構築子@{ i }
.

Definition 冪乗@{ i | }
  : 三段階のブラウワー順序数@{ i } -> 三段階のブラウワー順序数@{ i } -> 三段階のブラウワー順序数@{ i }
  :=
    fun x : 三段階のブラウワー順序数@{ i } =>
    簡易版の場合分け@{ i }
      三段階のブラウワー順序数@{ i }
      ( 後者関数@{ i } ゼロ@{ i } )
      ( fun a_前者 : 三段階のブラウワー順序数@{ i } => 乗算@{ i } a_前者 x )
      二段階の構築子@{ i }
.

Definition 二段階のブラウワー順序数を埋め込む@{ i | }
  : 二段階のブラウワー順序数@{ i } -> 三段階のブラウワー順序数@{ i }
  :=
    二段階のブラウワー順序数.場合分け@{ i }
      三段階のブラウワー順序数@{ i }
      ゼロ段階の構築子@{ i }
      一段階の構築子@{ i }
.

Definition 繰り返し適用の強上限@{ i | }
  :
    三段階のブラウワー順序数@{ i }
    ->
    ( 三段階のブラウワー順序数@{ i } -> 三段階のブラウワー順序数@{ i } )
    ->
    三段階のブラウワー順序数@{ i }
  :=
    fun x : 三段階のブラウワー順序数@{ i } =>
    fun f : 三段階のブラウワー順序数@{ i } -> 三段階のブラウワー順序数@{ i } =>
    二段階の構築子@{ i } ( 二段階のブラウワー順序数.簡易版の場合分け@{ i } 三段階のブラウワー順序数@{ i } x f )
.

Definition オメガ@{ i | } : 三段階のブラウワー順序数@{ i }
  := 繰り返し適用の強上限@{ i } ゼロ@{ i } 後者関数@{ i }
.

Definition オメガ冪@{ i | } : 三段階のブラウワー順序数@{ i } -> 三段階のブラウワー順序数@{ i }
  := 冪乗@{ i } オメガ@{ i }
.

Definition エプシロン数@{ i | } : 三段階のブラウワー順序数@{ i } -> 三段階のブラウワー順序数@{ i }
  :=
    簡易版の場合分け@{ i }
      三段階のブラウワー順序数@{ i }
      ( 繰り返し適用の強上限@{ i } ゼロ@{ i } オメガ冪@{ i } )
      (
        fun a_前者 : 三段階のブラウワー順序数@{ i } =>
        繰り返し適用の強上限@{ i } ( 後者関数@{ i } a_前者 ) オメガ冪@{ i }
      )
      二段階の構築子@{ i }
.

Definition ヴェブレン階層@{ i | }
  : 三段階のブラウワー順序数@{ i } -> 三段階のブラウワー順序数@{ i } -> 三段階のブラウワー順序数@{ i }
  :=
    簡易版の場合分け@{ i }
      ( 三段階のブラウワー順序数@{ i } -> 三段階のブラウワー順序数@{ i } )
      オメガ冪@{ i }
      (
        fun a_前者 : 三段階のブラウワー順序数@{ i } -> 三段階のブラウワー順序数 =>
        簡易版の場合分け@{ i }
          三段階のブラウワー順序数@{ i }
          ( 繰り返し適用の強上限@{ i } ゼロ@{ i } a_前者 )
          (
            fun b_前者 : 三段階のブラウワー順序数@{ i } =>
            繰り返し適用の強上限@{ i } ( 後者関数@{ i } b_前者 ) a_前者
          )
          二段階の構築子@{ i }
      )
      (
        fun
          a_二段階の列
            : 二段階のブラウワー順序数@{ i } -> 三段階のブラウワー順序数@{ i } -> 三段階のブラウワー順序数
        =>
        簡易版の場合分け@{ i }
          三段階のブラウワー順序数@{ i }
          ( 二段階の構築子@{ i } ( fun 添字 : 二段階のブラウワー順序数@{ i } => a_二段階の列 添字 ゼロ@{ i } ) )
          (
            fun b_前者 : 三段階のブラウワー順序数@{ i } =>
            二段階の構築子@{ i }
              ( fun 添字 : 二段階のブラウワー順序数@{ i } => a_二段階の列 添字 ( 後者関数@{ i } b_前者 ) )
          )
          二段階の構築子@{ i }
      )
.

End 三段階のブラウワー順序数 .

Definition 三段階のブラウワー順序数@{ i | } : Type@{ i }
  := 三段階のブラウワー順序数.三段階のブラウワー順序数@{ i }
.

Module 四段階のブラウワー順序数 .

Inductive 四段階のブラウワー順序数@{ i | } : Type@{ i }
  :=
    ゼロ段階の構築子 : ( ゼロ段階のブラウワー順序数@{ i } -> 四段階のブラウワー順序数 ) -> 四段階のブラウワー順序数
    |
    一段階の構築子 : ( 一段階のブラウワー順序数@{ i } -> 四段階のブラウワー順序数 ) -> 四段階のブラウワー順序数
    |
    二段階の構築子 : ( 二段階のブラウワー順序数@{ i } -> 四段階のブラウワー順序数 ) -> 四段階のブラウワー順序数
    |
    三段階の構築子 : ( 三段階のブラウワー順序数@{ i } -> 四段階のブラウワー順序数 ) -> 四段階のブラウワー順序数
.

Definition 場合分け@{ i | }
  :
    forall 目標 : Type@{ i } ,
    ( ( ゼロ段階のブラウワー順序数@{ i } -> 目標 ) -> 目標 )
    ->
    ( ( 一段階のブラウワー順序数@{ i } -> 目標 ) -> 目標 )
    ->
    ( ( 二段階のブラウワー順序数@{ i } -> 目標 ) -> 目標 )
    ->
    ( ( 三段階のブラウワー順序数@{ i } -> 目標 ) -> 目標 )
    ->
    四段階のブラウワー順序数@{ i }
    ->
    目標
  :=
    fun 目標 : Type@{ i } =>
    fun ゼロ段階の構築子の処理 : ( ゼロ段階のブラウワー順序数@{ i } -> 目標 ) -> 目標 =>
    fun 一段階の構築子の処理 : ( 一段階のブラウワー順序数@{ i } -> 目標 ) -> 目標 =>
    fun 二段階の構築子の処理 : ( 二段階のブラウワー順序数@{ i } -> 目標 ) -> 目標 =>
    fun 三段階の構築子の処理 : ( 三段階のブラウワー順序数@{ i } -> 目標 ) -> 目標 =>
    fix a ( 対象 : 四段階のブラウワー順序数@{ i } ) { struct 対象 } : 目標
      :=
        match
          対象
        with
          ゼロ段階の構築子 対象_ゼロ段階の列
          =>
          ゼロ段階の構築子の処理 ( fun 添字 : ゼロ段階のブラウワー順序数@{ i } => a ( 対象_ゼロ段階の列 添字 ) )
          |
          一段階の構築子 対象_一段階の列
          =>
          一段階の構築子の処理 ( fun 添字 : 一段階のブラウワー順序数@{ i } => a ( 対象_一段階の列 添字 ) )
          |
          二段階の構築子 対象_二段階の列
          =>
          二段階の構築子の処理 ( fun 添字 : 二段階のブラウワー順序数@{ i } => a ( 対象_二段階の列 添字 ) )
          |
          三段階の構築子 対象_三段階の列
          =>
          三段階の構築子の処理 ( fun 添字 : 三段階のブラウワー順序数@{ i } => a ( 対象_三段階の列 添字 ) )
        end
.

Definition 簡易版の場合分け@{ i | }
  :
    forall 目標 : Type@{ i } ,
    目標
    ->
    ( 目標 -> 目標 )
    ->
    ( ( 二段階のブラウワー順序数@{ i } -> 目標 ) -> 目標 )
    ->
    ( ( 三段階のブラウワー順序数@{ i } -> 目標 ) -> 目標 )
    ->
    四段階のブラウワー順序数@{ i }
    ->
    目標
  :=
    fun 目標 : Type@{ i } =>
    fun ゼロ段階の構築子の処理 : 目標 =>
    fun 一段階の構築子の処理 : 目標 -> 目標 =>
    fun 二段階の構築子の処理 : ( 二段階のブラウワー順序数@{ i } -> 目標 ) -> 目標 =>
    fun 三段階の構築子の処理 : ( 三段階のブラウワー順序数@{ i } -> 目標 ) -> 目標 =>
    場合分け@{ i }
      目標
      ( fun 対象_ゼロ段階の列 : ゼロ段階のブラウワー順序数@{ i } -> 目標 => ゼロ段階の構築子の処理 )
      (
        fun 対象_一段階の列 : 一段階のブラウワー順序数@{ i } -> 目標 =>
        一段階の構築子の処理 ( 対象_一段階の列 一段階のブラウワー順序数.ゼロ@{ i } )
      )
      二段階の構築子の処理
      三段階の構築子の処理
.

Definition ゼロ段階のブラウワー順序数を埋め込む@{ i | }
  : ゼロ段階のブラウワー順序数@{ i } -> 四段階のブラウワー順序数@{ i }
  := ゼロ段階のブラウワー順序数.場合分け@{ i } 四段階のブラウワー順序数@{ i }
.

Definition ゼロ@{ i | } : 四段階のブラウワー順序数@{ i }
  := ゼロ段階の構築子@{ i } ( ゼロ段階のブラウワー順序数.場合分け@{ i } 四段階のブラウワー順序数@{ i } )
.

Definition 一段階のブラウワー順序数を埋め込む@{ i | }
  : 一段階のブラウワー順序数@{ i } -> 四段階のブラウワー順序数@{ i }
  := 一段階のブラウワー順序数.場合分け@{ i } 四段階のブラウワー順序数@{ i } ゼロ段階の構築子@{ i }
.

Definition 後者関数@{ i | } : 四段階のブラウワー順序数@{ i } -> 四段階のブラウワー順序数@{ i }
  :=
    fun x : 四段階のブラウワー順序数@{ i } =>
    一段階の構築子@{ i } ( 一段階のブラウワー順序数.簡易版の場合分け@{ i } 四段階のブラウワー順序数@{ i } x )
.

Definition 加算@{ i | }
  : 四段階のブラウワー順序数@{ i } -> 四段階のブラウワー順序数@{ i } -> 四段階のブラウワー順序数@{ i }
  :=
    fun x : 四段階のブラウワー順序数@{ i } =>
    簡易版の場合分け@{ i }
      四段階のブラウワー順序数@{ i }
      x
      後者関数@{ i }
      二段階の構築子@{ i }
      三段階の構築子@{ i }
.

Definition 乗算@{ i | }
  : 四段階のブラウワー順序数@{ i } -> 四段階のブラウワー順序数@{ i } -> 四段階のブラウワー順序数@{ i }
  :=
    fun x : 四段階のブラウワー順序数@{ i } =>
    簡易版の場合分け@{ i }
      四段階のブラウワー順序数@{ i }
      ゼロ@{ i }
      ( fun a_前者 : 四段階のブラウワー順序数@{ i } => 加算@{ i } a_前者 x )
      二段階の構築子@{ i }
      三段階の構築子@{ i }
.

Definition 冪乗@{ i | }
  : 四段階のブラウワー順序数@{ i } -> 四段階のブラウワー順序数@{ i } -> 四段階のブラウワー順序数@{ i }
  :=
    fun x : 四段階のブラウワー順序数@{ i } =>
    簡易版の場合分け@{ i }
      四段階のブラウワー順序数@{ i }
      ( 後者関数@{ i } ゼロ@{ i } )
      ( fun a_前者 : 四段階のブラウワー順序数@{ i } => 乗算@{ i } a_前者 x )
      二段階の構築子@{ i }
      三段階の構築子@{ i }
.

Definition 二段階のブラウワー順序数を埋め込む@{ i | }
  : 二段階のブラウワー順序数@{ i } -> 四段階のブラウワー順序数@{ i }
  :=
    二段階のブラウワー順序数.場合分け@{ i }
      四段階のブラウワー順序数@{ i }
      ゼロ段階の構築子@{ i }
      一段階の構築子@{ i }
.

Definition 繰り返し適用の強上限@{ i | }
  :
    四段階のブラウワー順序数@{ i }
    ->
    ( 四段階のブラウワー順序数@{ i } -> 四段階のブラウワー順序数@{ i } )
    ->
    四段階のブラウワー順序数@{ i }
  :=
    fun x : 四段階のブラウワー順序数@{ i } =>
    fun f : 四段階のブラウワー順序数@{ i } -> 四段階のブラウワー順序数@{ i } =>
    二段階の構築子@{ i } ( 二段階のブラウワー順序数.簡易版の場合分け@{ i } 四段階のブラウワー順序数@{ i } x f )
.

Definition オメガ@{ i | } : 四段階のブラウワー順序数@{ i }
  := 繰り返し適用の強上限@{ i } ゼロ@{ i } 後者関数@{ i }
.

Definition オメガ冪@{ i | } : 四段階のブラウワー順序数@{ i } -> 四段階のブラウワー順序数@{ i }
  := 冪乗@{ i } オメガ@{ i }
.

Definition エプシロン数@{ i | } : 四段階のブラウワー順序数@{ i } -> 四段階のブラウワー順序数@{ i }
  :=
    簡易版の場合分け@{ i }
      四段階のブラウワー順序数@{ i }
      ( 繰り返し適用の強上限@{ i } ゼロ@{ i } オメガ冪@{ i } )
      (
        fun a_前者 : 四段階のブラウワー順序数@{ i } =>
        繰り返し適用の強上限@{ i } ( 後者関数@{ i } a_前者 ) オメガ冪@{ i }
      )
      二段階の構築子@{ i }
      三段階の構築子@{ i }
.

Definition ヴェブレン階層@{ i | }
  : 四段階のブラウワー順序数@{ i } -> 四段階のブラウワー順序数@{ i } -> 四段階のブラウワー順序数@{ i }
  :=
    簡易版の場合分け@{ i }
      ( 四段階のブラウワー順序数@{ i } -> 四段階のブラウワー順序数@{ i } )
      オメガ冪@{ i }
      (
        fun a_前者 : 四段階のブラウワー順序数@{ i } -> 四段階のブラウワー順序数 =>
        簡易版の場合分け@{ i }
          四段階のブラウワー順序数@{ i }
          ( 繰り返し適用の強上限@{ i } ゼロ@{ i } a_前者 )
          (
            fun b_前者 : 四段階のブラウワー順序数@{ i } =>
            繰り返し適用の強上限@{ i } ( 後者関数@{ i } b_前者 ) a_前者
          )
          二段階の構築子@{ i }
          三段階の構築子@{ i }
      )
      (
        fun
          a_二段階の列
            : 二段階のブラウワー順序数@{ i } -> 四段階のブラウワー順序数@{ i } -> 四段階のブラウワー順序数
        =>
        簡易版の場合分け@{ i }
          四段階のブラウワー順序数@{ i }
          ( 二段階の構築子@{ i } ( fun 添字 : 二段階のブラウワー順序数@{ i } => a_二段階の列 添字 ゼロ@{ i } ) )
          (
            fun b_前者 : 四段階のブラウワー順序数@{ i } =>
            二段階の構築子@{ i }
              ( fun 添字 : 二段階のブラウワー順序数@{ i } => a_二段階の列 添字 ( 後者関数@{ i } b_前者 ) )
          )
          二段階の構築子@{ i }
          三段階の構築子@{ i }
      )
      (
        fun
          a_三段階の列
            : 三段階のブラウワー順序数@{ i } -> 四段階のブラウワー順序数@{ i } -> 四段階のブラウワー順序数
        =>
        簡易版の場合分け@{ i }
          四段階のブラウワー順序数@{ i }
          ( 三段階の構築子@{ i } ( fun 添字 : 三段階のブラウワー順序数@{ i } => a_三段階の列 添字 ゼロ@{ i } ) )
          (
            fun b_前者 : 四段階のブラウワー順序数@{ i } =>
            三段階の構築子@{ i }
              ( fun 添字 : 三段階のブラウワー順序数@{ i } => a_三段階の列 添字 ( 後者関数@{ i } b_前者 ) )
          )
          二段階の構築子@{ i }
          三段階の構築子@{ i }
      )
.

Definition 三段階のブラウワー順序数を埋め込む@{ i | }
  : 三段階のブラウワー順序数@{ i } -> 四段階のブラウワー順序数@{ i }
  :=
    三段階のブラウワー順序数.場合分け@{ i }
      四段階のブラウワー順序数@{ i }
      ゼロ段階の構築子@{ i }
      一段階の構築子@{ i }
      二段階の構築子@{ i }
.

Definition 一番目のオメガ@{ i } : 四段階のブラウワー順序数@{ i }
  := 三段階の構築子@{ i } 三段階のブラウワー順序数を埋め込む@{ i }
.

End 四段階のブラウワー順序数 .

Definition 四段階のブラウワー順序数@{ i | } : Type@{ i }
  := 四段階のブラウワー順序数.四段階のブラウワー順序数@{ i }
.

Module 五段階のブラウワー順序数 .

Inductive 五段階のブラウワー順序数@{ i | } : Type@{ i }
  :=
    ゼロ段階の構築子 : ( ゼロ段階のブラウワー順序数@{ i } -> 五段階のブラウワー順序数 ) -> 五段階のブラウワー順序数
    |
    一段階の構築子 : ( 一段階のブラウワー順序数@{ i } -> 五段階のブラウワー順序数 ) -> 五段階のブラウワー順序数
    |
    二段階の構築子 : ( 二段階のブラウワー順序数@{ i } -> 五段階のブラウワー順序数 ) -> 五段階のブラウワー順序数
    |
    三段階の構築子 : ( 三段階のブラウワー順序数@{ i } -> 五段階のブラウワー順序数 ) -> 五段階のブラウワー順序数
    |
    四段階の構築子 : ( 四段階のブラウワー順序数@{ i } -> 五段階のブラウワー順序数 ) -> 五段階のブラウワー順序数
.

Definition 場合分け@{ i | }
  :
    forall 目標 : Type@{ i } ,
    ( ( ゼロ段階のブラウワー順序数@{ i } -> 目標 ) -> 目標 )
    ->
    ( ( 一段階のブラウワー順序数@{ i } -> 目標 ) -> 目標 )
    ->
    ( ( 二段階のブラウワー順序数@{ i } -> 目標 ) -> 目標 )
    ->
    ( ( 三段階のブラウワー順序数@{ i } -> 目標 ) -> 目標 )
    ->
    ( ( 四段階のブラウワー順序数@{ i } -> 目標 ) -> 目標 )
    ->
    五段階のブラウワー順序数@{ i }
    ->
    目標
  :=
    fun 目標 : Type@{ i } =>
    fun ゼロ段階の構築子の処理 : ( ゼロ段階のブラウワー順序数@{ i } -> 目標 ) -> 目標 =>
    fun 一段階の構築子の処理 : ( 一段階のブラウワー順序数@{ i } -> 目標 ) -> 目標 =>
    fun 二段階の構築子の処理 : ( 二段階のブラウワー順序数@{ i } -> 目標 ) -> 目標 =>
    fun 三段階の構築子の処理 : ( 三段階のブラウワー順序数@{ i } -> 目標 ) -> 目標 =>
    fun 四段階の構築子の処理 : ( 四段階のブラウワー順序数@{ i } -> 目標 ) -> 目標 =>
    fix a ( 対象 : 五段階のブラウワー順序数@{ i } ) { struct 対象 } : 目標
      :=
        match
          対象
        with
          ゼロ段階の構築子 対象_ゼロ段階の列
          =>
          ゼロ段階の構築子の処理 ( fun 添字 : ゼロ段階のブラウワー順序数@{ i } => a ( 対象_ゼロ段階の列 添字 ) )
          |
          一段階の構築子 対象_一段階の列
          =>
          一段階の構築子の処理 ( fun 添字 : 一段階のブラウワー順序数@{ i } => a ( 対象_一段階の列 添字 ) )
          |
          二段階の構築子 対象_二段階の列
          =>
          二段階の構築子の処理 ( fun 添字 : 二段階のブラウワー順序数@{ i } => a ( 対象_二段階の列 添字 ) )
          |
          三段階の構築子 対象_三段階の列
          =>
          三段階の構築子の処理 ( fun 添字 : 三段階のブラウワー順序数@{ i } => a ( 対象_三段階の列 添字 ) )
          |
          四段階の構築子 対象_四段階の列
          =>
          四段階の構築子の処理 ( fun 添字 : 四段階のブラウワー順序数@{ i } => a ( 対象_四段階の列 添字 ) )
        end
.

Definition 簡易版の場合分け@{ i | }
  :
    forall 目標 : Type@{ i } ,
    目標
    ->
    ( 目標 -> 目標 )
    ->
    ( ( 二段階のブラウワー順序数@{ i } -> 目標 ) -> 目標 )
    ->
    ( ( 三段階のブラウワー順序数@{ i } -> 目標 ) -> 目標 )
    ->
    ( ( 四段階のブラウワー順序数@{ i } -> 目標 ) -> 目標 )
    ->
    五段階のブラウワー順序数@{ i }
    ->
    目標
  :=
    fun 目標 : Type@{ i } =>
    fun ゼロ段階の構築子の処理 : 目標 =>
    fun 一段階の構築子の処理 : 目標 -> 目標 =>
    fun 二段階の構築子の処理 : ( 二段階のブラウワー順序数@{ i } -> 目標 ) -> 目標 =>
    fun 三段階の構築子の処理 : ( 三段階のブラウワー順序数@{ i } -> 目標 ) -> 目標 =>
    fun 四段階の構築子の処理 : ( 四段階のブラウワー順序数@{ i } -> 目標 ) -> 目標 =>
    場合分け@{ i }
      目標
      ( fun 対象_ゼロ段階の列 : ゼロ段階のブラウワー順序数@{ i } -> 目標 => ゼロ段階の構築子の処理 )
      (
        fun 対象_一段階の列 : 一段階のブラウワー順序数@{ i } -> 目標 =>
        一段階の構築子の処理 ( 対象_一段階の列 一段階のブラウワー順序数.ゼロ@{ i } )
      )
      二段階の構築子の処理
      三段階の構築子の処理
      四段階の構築子の処理
.

Definition ゼロ段階のブラウワー順序数を埋め込む@{ i | }
  : ゼロ段階のブラウワー順序数@{ i } -> 五段階のブラウワー順序数@{ i }
  := ゼロ段階のブラウワー順序数.場合分け@{ i } 五段階のブラウワー順序数@{ i }
.

Definition ゼロ@{ i | } : 五段階のブラウワー順序数@{ i }
  := ゼロ段階の構築子@{ i } ( ゼロ段階のブラウワー順序数.場合分け@{ i } 五段階のブラウワー順序数@{ i } )
.

Definition 一段階のブラウワー順序数を埋め込む@{ i | }
  : 一段階のブラウワー順序数@{ i } -> 五段階のブラウワー順序数@{ i }
  := 一段階のブラウワー順序数.場合分け@{ i } 五段階のブラウワー順序数@{ i } ゼロ段階の構築子@{ i }
.

Definition 後者関数@{ i | } : 五段階のブラウワー順序数@{ i } -> 五段階のブラウワー順序数@{ i }
  :=
    fun x : 五段階のブラウワー順序数@{ i } =>
    一段階の構築子@{ i } ( 一段階のブラウワー順序数.簡易版の場合分け@{ i } 五段階のブラウワー順序数@{ i } x )
.

Definition 加算@{ i | }
  : 五段階のブラウワー順序数@{ i } -> 五段階のブラウワー順序数@{ i } -> 五段階のブラウワー順序数@{ i }
  :=
    fun x : 五段階のブラウワー順序数@{ i } =>
    簡易版の場合分け@{ i }
      五段階のブラウワー順序数@{ i }
      x
      後者関数@{ i }
      二段階の構築子@{ i }
      三段階の構築子@{ i }
      四段階の構築子@{ i }
.

Definition 乗算@{ i | }
  : 五段階のブラウワー順序数@{ i } -> 五段階のブラウワー順序数@{ i } -> 五段階のブラウワー順序数@{ i }
  :=
    fun x : 五段階のブラウワー順序数@{ i } =>
    簡易版の場合分け@{ i }
      五段階のブラウワー順序数@{ i }
      ゼロ@{ i }
      ( fun a_前者 : 五段階のブラウワー順序数@{ i } => 加算@{ i } a_前者 x )
      二段階の構築子@{ i }
      三段階の構築子@{ i }
      四段階の構築子@{ i }
.

Definition 冪乗@{ i | }
  : 五段階のブラウワー順序数@{ i } -> 五段階のブラウワー順序数@{ i } -> 五段階のブラウワー順序数@{ i }
  :=
    fun x : 五段階のブラウワー順序数@{ i } =>
    簡易版の場合分け@{ i }
      五段階のブラウワー順序数@{ i }
      ( 後者関数@{ i } ゼロ@{ i } )
      ( fun a_前者 : 五段階のブラウワー順序数@{ i } => 乗算@{ i } a_前者 x )
      二段階の構築子@{ i }
      三段階の構築子@{ i }
      四段階の構築子@{ i }
.

Definition 二段階のブラウワー順序数を埋め込む@{ i | }
  : 二段階のブラウワー順序数@{ i } -> 五段階のブラウワー順序数@{ i }
  :=
    二段階のブラウワー順序数.場合分け@{ i }
      五段階のブラウワー順序数@{ i }
      ゼロ段階の構築子@{ i }
      一段階の構築子@{ i }
.

Definition 繰り返し適用の強上限@{ i | }
  :
    五段階のブラウワー順序数@{ i }
    ->
    ( 五段階のブラウワー順序数@{ i } -> 五段階のブラウワー順序数@{ i } )
    ->
    五段階のブラウワー順序数@{ i }
  :=
    fun x : 五段階のブラウワー順序数@{ i } =>
    fun f : 五段階のブラウワー順序数@{ i } -> 五段階のブラウワー順序数@{ i } =>
    二段階の構築子@{ i } ( 二段階のブラウワー順序数.簡易版の場合分け@{ i } 五段階のブラウワー順序数@{ i } x f )
.

Definition オメガ@{ i | } : 五段階のブラウワー順序数@{ i }
  := 繰り返し適用の強上限@{ i } ゼロ@{ i } 後者関数@{ i }
.

Definition オメガ冪@{ i | } : 五段階のブラウワー順序数@{ i } -> 五段階のブラウワー順序数@{ i }
  := 冪乗@{ i } オメガ@{ i }
.

Definition エプシロン数@{ i | } : 五段階のブラウワー順序数@{ i } -> 五段階のブラウワー順序数@{ i }
  :=
    簡易版の場合分け@{ i }
      五段階のブラウワー順序数@{ i }
      ( 繰り返し適用の強上限@{ i } ゼロ@{ i } オメガ冪@{ i } )
      (
        fun a_前者 : 五段階のブラウワー順序数@{ i } =>
        繰り返し適用の強上限@{ i } ( 後者関数@{ i } a_前者 ) オメガ冪@{ i }
      )
      二段階の構築子@{ i }
      三段階の構築子@{ i }
      四段階の構築子@{ i }
.

Definition ヴェブレン階層@{ i | }
  : 五段階のブラウワー順序数@{ i } -> 五段階のブラウワー順序数@{ i } -> 五段階のブラウワー順序数@{ i }
  :=
    簡易版の場合分け@{ i }
      ( 五段階のブラウワー順序数@{ i } -> 五段階のブラウワー順序数@{ i } )
      オメガ冪@{ i }
      (
        fun a_前者 : 五段階のブラウワー順序数@{ i } -> 五段階のブラウワー順序数 =>
        簡易版の場合分け@{ i }
          五段階のブラウワー順序数@{ i }
          ( 繰り返し適用の強上限@{ i } ゼロ@{ i } a_前者 )
          (
            fun b_前者 : 五段階のブラウワー順序数@{ i } =>
            繰り返し適用の強上限@{ i } ( 後者関数@{ i } b_前者 ) a_前者
          )
          二段階の構築子@{ i }
          三段階の構築子@{ i }
          四段階の構築子@{ i }
      )
      (
        fun
          a_二段階の列
            : 二段階のブラウワー順序数@{ i } -> 五段階のブラウワー順序数@{ i } -> 五段階のブラウワー順序数
        =>
        簡易版の場合分け@{ i }
          五段階のブラウワー順序数@{ i }
          ( 二段階の構築子@{ i } ( fun 添字 : 二段階のブラウワー順序数@{ i } => a_二段階の列 添字 ゼロ@{ i } ) )
          (
            fun b_前者 : 五段階のブラウワー順序数@{ i } =>
            二段階の構築子@{ i }
              ( fun 添字 : 二段階のブラウワー順序数@{ i } => a_二段階の列 添字 ( 後者関数@{ i } b_前者 ) )
          )
          二段階の構築子@{ i }
          三段階の構築子@{ i }
          四段階の構築子@{ i }
      )
      (
        fun
          a_三段階の列
            : 三段階のブラウワー順序数@{ i } -> 五段階のブラウワー順序数@{ i } -> 五段階のブラウワー順序数
        =>
        簡易版の場合分け@{ i }
          五段階のブラウワー順序数@{ i }
          ( 三段階の構築子@{ i } ( fun 添字 : 三段階のブラウワー順序数@{ i } => a_三段階の列 添字 ゼロ@{ i } ) )
          (
            fun b_前者 : 五段階のブラウワー順序数@{ i } =>
            三段階の構築子@{ i }
              ( fun 添字 : 三段階のブラウワー順序数@{ i } => a_三段階の列 添字 ( 後者関数@{ i } b_前者 ) )
          )
          二段階の構築子@{ i }
          三段階の構築子@{ i }
          四段階の構築子@{ i }
      )
      (
        fun
          a_四段階の列
            : 四段階のブラウワー順序数@{ i } -> 五段階のブラウワー順序数@{ i } -> 五段階のブラウワー順序数
        =>
        簡易版の場合分け@{ i }
          五段階のブラウワー順序数@{ i }
          ( 四段階の構築子@{ i } ( fun 添字 : 四段階のブラウワー順序数@{ i } => a_四段階の列 添字 ゼロ@{ i } ) )
          (
            fun b_前者 : 五段階のブラウワー順序数@{ i } =>
            四段階の構築子@{ i }
              ( fun 添字 : 四段階のブラウワー順序数@{ i } => a_四段階の列 添字 ( 後者関数@{ i } b_前者 ) )
          )
          二段階の構築子@{ i }
          三段階の構築子@{ i }
          四段階の構築子@{ i }
      )
.

Definition 三段階のブラウワー順序数を埋め込む@{ i | }
  : 三段階のブラウワー順序数@{ i } -> 五段階のブラウワー順序数@{ i }
  :=
    三段階のブラウワー順序数.場合分け@{ i }
      五段階のブラウワー順序数@{ i }
      ゼロ段階の構築子@{ i }
      一段階の構築子@{ i }
      二段階の構築子@{ i }
.

Definition 一番目のオメガ@{ i } : 五段階のブラウワー順序数@{ i }
  := 三段階の構築子@{ i } 三段階のブラウワー順序数を埋め込む@{ i }
.

Definition 四段階のブラウワー順序数を埋め込む@{ i | }
  : 四段階のブラウワー順序数@{ i } -> 五段階のブラウワー順序数@{ i }
  :=
    四段階のブラウワー順序数.場合分け@{ i }
      五段階のブラウワー順序数@{ i }
      ゼロ段階の構築子@{ i }
      一段階の構築子@{ i }
      二段階の構築子@{ i }
      三段階の構築子@{ i }
.

Definition 二番目のオメガ@{ i } : 五段階のブラウワー順序数@{ i }
  := 四段階の構築子@{ i } 四段階のブラウワー順序数を埋め込む@{ i }
.

End 五段階のブラウワー順序数 .

Definition 五段階のブラウワー順序数@{ i | } : Type@{ i }
  := 五段階のブラウワー順序数.五段階のブラウワー順序数@{ i }
.

Module 順序数崩壊関数その一 .

Import 四段階のブラウワー順序数 .

Definition オメガ冪@{ i | }
  : 四段階のブラウワー順序数@{ i } -> 四段階のブラウワー順序数@{ i }
  :=
    簡易版の場合分け@{ i }
      四段階のブラウワー順序数@{ i }
      ( 後者関数@{ i } ゼロ@{ i } )
      (
        fun a_前者 : 四段階のブラウワー順序数@{ i } =>
        繰り返し適用の強上限@{ i }
          ( 加算@{ i } a_前者 a_前者 )
          ( fun y => 加算@{ i } y a_前者 )
      )
      二段階の構築子@{ i }
      三段階の構築子@{ i }
.

Definition ヴェブレン階層@{ i | }
  : 四段階のブラウワー順序数@{ i } -> 四段階のブラウワー順序数@{ i } -> 四段階のブラウワー順序数@{ i }
  :=
    簡易版の場合分け@{ i }
      ( 四段階のブラウワー順序数@{ i } -> 四段階のブラウワー順序数@{ i } )
      オメガ冪@{ i }
      (
        fun a_前者 : 四段階のブラウワー順序数@{ i } -> 四段階のブラウワー順序数 =>
        簡易版の場合分け@{ i }
          四段階のブラウワー順序数@{ i }
          ( 繰り返し適用の強上限@{ i } ゼロ@{ i } a_前者 )
          (
            fun b_前者 : 四段階のブラウワー順序数@{ i } =>
            繰り返し適用の強上限@{ i } ( 後者関数@{ i } b_前者 ) a_前者
          )
          二段階の構築子@{ i }
          三段階の構築子@{ i }
      )
      (
        fun
          a_二段階の列
            : 二段階のブラウワー順序数@{ i } -> 四段階のブラウワー順序数@{ i } -> 四段階のブラウワー順序数
        =>
        簡易版の場合分け@{ i }
          四段階のブラウワー順序数@{ i }
          ( 二段階の構築子@{ i } ( fun 添字 : 二段階のブラウワー順序数@{ i } => a_二段階の列 添字 ゼロ@{ i } ) )
          (
            fun b_前者 : 四段階のブラウワー順序数@{ i } =>
            二段階の構築子@{ i }
              ( fun 添字 : 二段階のブラウワー順序数@{ i } => a_二段階の列 添字 ( 後者関数@{ i } b_前者 ) )
          )
          二段階の構築子@{ i }
          三段階の構築子@{ i }
      )
      (
        fun
          a_三段階の列
            : 三段階のブラウワー順序数@{ i } -> 四段階のブラウワー順序数@{ i } -> 四段階のブラウワー順序数
        =>
        簡易版の場合分け@{ i }
          四段階のブラウワー順序数@{ i }
          ( 三段階の構築子@{ i } ( fun 添字 : 三段階のブラウワー順序数@{ i } => a_三段階の列 添字 ゼロ@{ i } ) )
          (
            fun b_前者 : 四段階のブラウワー順序数@{ i } =>
            三段階の構築子@{ i }
              ( fun 添字 : 三段階のブラウワー順序数@{ i } => a_三段階の列 添字 ( 後者関数@{ i } b_前者 ) )
          )
          二段階の構築子@{ i }
          三段階の構築子@{ i }
      )
.

End 順序数崩壊関数その一 .

End Part_1 .
