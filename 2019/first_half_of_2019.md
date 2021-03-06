# 2019上半期の巨大数界隈での活動

私が巨大数をやり始めたのは2018年12月の時でした。それから、もう９ヶ月経ちました。長いのか短いのかよく判りませんが、楽しかったということは確かでした。ふと思い立ったので今までの活動の記録を記事に纏めたいと思います。

## 巨大数 Advent Calendar 2018

みんなが一日ずつ巨大数を投稿するイベントです。アドベントカレンダーは、クリスマスまで一日ずつ日を数えていく文化に由来する、12月1日から25日まで何人かで一日一記事を投稿していくというイベントの形式です。これを巨大数というテーマに行うにあたって、「最後に全投稿の総和を取って新しい巨大数を作る」「使ってもいい関数は四則演算と自分自身で定義したものとカレンダー内で定義されたものだけ」などの要素が加えられました。イベントはADVENTARというサービスの上で行われました（[リンク](https://adventar.org/calendars/3314)）。このイベントは[p進大好きbot](https://twitter.com/non_archimedean)さんのツイートが発端になって開催されました。私は、このイベントに参加することによって巨大数の世界に足を踏み入れました。具体的な開催の経緯は次の通りです。

1. p進大好きbotの[ツイート](https://twitter.com/non_archimedean/status/1060365003297972224)で「巨大数アドベントカレンダー」のアイデアが出される。
1. 巨大数大好きbotの[返信](https://twitter.com/GoogologyBot/status/1060375254814478342)がツイートされる。
1. p進大好きbotの[返信](https://twitter.com/non_archimedean/status/1060385460059402240)がツイートされる。
1. 巨大数大好きbotの[返信](https://twitter.com/GoogologyBot/status/1060386621613199360)でアドベントカレンダー作成の報告が行われる。
1. [ｷｪｪｪｪｪｪｪ](https://twitter.com/non_archimedean/status/1060412474481008642)

参加者は p進大好きbot (25日の内24日で投稿) と Hexirp (25日の内1日で投稿) の二人のみでした。私が投稿した巨大数のコンセプトは「Coqで定義されているから絶対に well-defined な巨大数」でした。初めは強さを急増加関数で $ \\omega ^ { \\omega ^ 2 } $ と解析していましたが、後の再解析で強さが $ \\omega ^ 4 $ しかないことが分かりました。

私はこのイベントに参加することによって、巨大数の世界に足を踏み入れました。思い出深いイベントです。

## Coqで巨大数

巨大数 Advent Calendar 2018 に巨大数を投稿した後、私は巨大数からしばらく離れていました。[この記事](https://googology.wikia.org/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:Hexirp/Coq%E3%81%A7%E5%B7%A8%E5%A4%A7%E6%95%B0)は、ちょうど戻ってきたときに作ったものです。

前にアドベントカレンダーに投稿した巨大数が、Coqでやる動機などが説明不足だと感じたため記事にしたものです。この記事がCoqの基礎となっている predicative Calculus of Inductive Constructions (pCIC) という体系を広めたみたいです。やっぱり ZFC plus countably many inaccessibles と同じ強さっていうのはインパクトがあったのかなと思っています。ただ、ローダー数で使われる Calculus of Constructions (CoC) という体系との混同が起こっているみたいで心配です。

この記事のコメントでのp進大好きbotさんのやり取りで、Coqで定義した巨大数を東方巨大数3に投稿するとしていましたが、結局投稿しませんでした（普通の巨大数自体は投稿した）。

## ハイパー演算子の拡張

私が思い付けるだけのハイパー演算子の拡張を書き並べた[記事](https://googology.wikia.org/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:Hexirp/%E3%83%8F%E3%82%A4%E3%83%91%E3%83%BC%E6%BC%94%E7%AE%97%E5%AD%90%E3%81%AE%E6%8B%A1%E5%BC%B5)です。最初は殆どアイデアだけで定義はありませんでしたが、少しずつ書き加えていって全ての定義を埋めるに至りました。そのあとも2019年5月~6月と2019年6月~7月に二度の全体的な定義の変更を行いました。

変更するたびに厳密な定義へ書き換えていき、最後の定義はガッチガチの厳密な定義になったと思います。超限弱ハイパー演算子はかなり大きくなりそうだったので、次のブログ記事で解析を行いました。

## 超限ハイパー演算子の解析

超限弱ハイパー演算子の解析をする[記事](https://googology.wikia.org/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:Hexirp/%E8%B6%85%E9%99%90%E3%83%8F%E3%82%A4%E3%83%91%E3%83%BC%E6%BC%94%E7%AE%97%E5%AD%90%E3%81%AE%E8%A7%A3%E6%9E%90)です。初期段階では $ ω [ ω ] ω = SVO $ と予想していましたが、最後まで解析を進めると $ \\sup \\{ \\omega, \\omega [ \\omega ] \\omega, \\omega [ \\omega [ \\omega ] \\omega ] \\omega, \\ldots \\} = \\Gamma _ 0 $ となりました。しかし、超限弱ハイパー演算子を東方巨大数３に投稿したときの巨大数大好きbotさんによる[解析結果](https://docs.google.com/spreadsheets/d/13dF_JysGD8shMOTYL3KfsFmcKOMNXp7hyfgjVbQZm6I/edit#gid=206312705)では $ \\sup \\{ \\omega, \\omega [ \\omega ] \\omega, \\omega [ \\omega [ \\omega ] \\omega ] \\omega, \\ldots \\} = \\varphi ( \\omega + 1, 0 ) $ となりました。

これは $ ω [ ω + 1 ] ω [ ω ] ω $ で折れ曲がっていたためです。期待した結果にはなりませんでしたが定義が美しいものだったので投稿の修正はしないことにしました。のちに $ Γ _ 0 $ に到達するように変更したものを別個に定義しています。解析をミスったのはたぶん経験不足ですが、東方巨大数３審査員に解析される前に急いで自分で解析してしまえと急いだせいかもしれません。

## 数符「トランスウィークハイパー」

東方巨大数３への投稿のための[記事](https://googology.wikia.org/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:Hexirp/%E6%95%B0%E7%AC%A6%E3%80%8C%E3%83%88%E3%83%A9%E3%83%B3%E3%82%B9%E3%82%A6%E3%82%A3%E3%83%BC%E3%82%AF%E3%83%8F%E3%82%A4%E3%83%91%E3%83%BC%E3%80%8D)でした。超限弱ハイパー演算子を計算可能な形に置き換えて定義したものです。定義に粗をいくつか見つけており、大きさは十分なものの不完全な状態だと考えています。ちなみに、この名前は自信作でした。

この記事自体がエントリーの定義であり、東方巨大数３では計算可能関数部門８位という結果になりました。微妙な結果でしたが well-defined でなかなかの大きさだったので満足です。

## 順序数解析でのOCFの上位辺りについてメモ

順序数解析でのOCFの上位辺りについて調べた結果をメモした[記事](https://googology.wikia.org/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:Hexirp/%E9%A0%86%E5%BA%8F%E6%95%B0%E8%A7%A3%E6%9E%90%E3%81%A7%E3%81%AEOCF%E3%81%AE%E4%B8%8A%E4%BD%8D%E8%BE%BA%E3%82%8A%E3%81%AB%E3%81%A4%E3%81%84%E3%81%A6%E3%83%A1%E3%83%A2)です。内容は非常に不正確なものの、メモであるからして問題はないと考えています。各自は信用しないようにお願いします。

## 計算不可能関数のより細かい階層について

チャーチ＝クリーネ順序数がうまく働かないことが判明したので、新たな尺度がないかと立ち上げた[スレッド](https://googology.wikia.org/ja/wiki/%E3%82%B9%E3%83%AC%E3%83%83%E3%83%89:3876)です。スレッドは途中で止まっていますが、私の結論としては n 次ビジービーバー関数で測るか $ \\mathbf{0}^{(\\alpha)} $ で測るかです。

## バシク行列を Haskell に移植

タイトル通りの[記事](https://googology.wikia.org/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:Hexirp/%E3%83%90%E3%82%B7%E3%82%AF%E8%A1%8C%E5%88%97%E3%82%92_Haskell_%E3%81%AB%E7%A7%BB%E6%A4%8D)です。

プログラムには少し工夫を加えていて、インデックスを次のように反転させました。このほうが Haskell では書きやすくなります。

  x30 x20 x10 x00
  x31 x21 x11 x01
  x32 x22 x12 x02

## 順序数で順序数を解析する

順序数で順序数を解析しようとする人が少なくないかと思って始めた[プロジェクト](https://googology.wikia.org/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:Hexirp/%E9%A0%86%E5%BA%8F%E6%95%B0%E3%81%A7%E9%A0%86%E5%BA%8F%E6%95%B0%E3%82%92%E8%A7%A3%E6%9E%90%E3%81%99%E3%82%8B)です。最終的な目標は Rathjen ψ ですが、その他にも気が向いたら色々やろうと思っています。

## 急増加関数の変種

急増加関数の変種を思い付けるだけ書き並べた[記事](https://googology.wikia.org/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:Hexirp/%E6%80%A5%E5%A2%97%E5%8A%A0%E9%96%A2%E6%95%B0%E3%81%AE%E5%A4%89%E7%A8%AE)です。この記事に触発されて Hassium108 さんが 2-短成長階層を[考案](https://twitter.com/1Hassium/status/1151038370312871936)し、それもこの記事の中に追記されています。なお、この名称は私が考案して Hassium108 さんに採用していただいたものです。

## 「シラン数第四形態改二」の定義

みんなで作ろう巨大数の定義部門への参加記事です。定義対象は Hassium108 さんが投稿した[シラン数第四形態改二](https://twitter.com/1Hassium/status/1152881969652359168)であり、三種類の定義が記事内で行われています。

定義１はTREE数列をベースにしています。この定義の停止性はTREE数列の停止性の証明と同じように証明可能であり well-defined です。また、そのためシステムの強さは $ ε\\\_ω $ を超えているので課せられた条件を満たしています。定義２はサブキュービックグラフ数のシステムからサブキュービックであるという条件を取り除いたものです。そのため well-defined であるかどうかは不明ですが、もしそうならその強さは $ ε\\\_ω $ を超えていることは確実です。定義３は定義２の条件を一部分変更して構造を潰したものです。おそらく巡回路がないグラフの範囲ではとても弱くなっています。それでいてシステム自体の強さは巡回路があるグラフで伸びていき定義２に届く、と考えています。

定義３は 構想 No. 6 定義 No. 6 であり、さらに値が 6 というゾロ目を狙うために急遽作成したものです。また、これは定義２を考えているときに思い付いたものの弱くなりすぎると気づいて捨てた定義でした。

## メモ

色々な[メモ](https://googology.wikia.org/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC:Hexirp/%E3%83%A1%E3%83%A2)です。ブログ記事ではないのですが、ここでも無視できないほど色々やっているので紹介します。誰かがもっと詳しくやってくれないか期待しています。
