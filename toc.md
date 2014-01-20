# Coinitial semantics for redecoration of triangular matrices

This table of contents give pointers in the Coq formalisation following the sectioning of the [paper](http://arxiv.org/abs/1401.1053)

## Preliminaries

* [Category definition][Category]
* [Category of Sets][Set]
* [Category of Setoids][Setoid]
* [Functor 𝑬𝑸 : Set -> Setoid][EQ]
* [Cartesian strong monoidal functors][SMF]
  * [Functor 𝑬𝑸 is strong monoidal][SM_EQ]

## Relative comonads and their morphisms

* [Relative comonad definition][RC]
* [Functoriality of relative comonads][FRC]
* [Morphism of relative comonads][MRC]
* [Category of relative comonads][CRC]

## Comodules over relative comonads

* [Comodule over a relative comonad definition][CM]
* [Functoriality of comodules][FCM]
* [Morphism of comodules][MCM]
* [Category of comodules][CMC]
* [Tautological comodule][TCM]
* [Pushforward comodule][PCM]
* [Morphism of comonads induces morphism of comodules][ICM]

## Coalgebras for infinite triangular matrices

* [Relative comonad with cut definition][RCC]
* [Morphism of relative comonads with cut][MRCC]
* [Category of relative comonads with cut][CRCC]
* [Canonical cut operation][CCRCC]
* [Precomposition with product][PRCC]
* [Pushforward commutes with precomposition with product][PCRCC]
* [Category of triangular matrices][TM]
* [Coinitial semantics for triangular matrices with redecoration][CS]


[Category]: Cat.Theory.Category.html#Category
[Set]: Cat.Category.Sets.html#𝑺𝒆𝒕
[EQ]: Cat.Category.Sets_Setoids.html#𝑬𝑸
[Setoid]: Cat.Category.Setoids.html#𝑺𝒆𝒕𝒐𝒊𝒅
[SMF]: Cat.Theory.CartesianStrongMonoidal.html#CartesianStrongMonoidal
[SM_EQ]: Cat.Category.Sets_Setoids.html#𝑬𝑸_SM
[RC]: Cat.Theory.RelativeComonad.html#RelativeComonad
[FRC]: Cat.Theory.RelativeComonad.html#Functoriality
[MRC]: Cat.Theory.RelativeComonad.html#Morphism
[CRC]: Cat.Category.RComonad.html#𝑹𝑪𝒐𝒎𝒐𝒏𝒂𝒅
[CM]: Cat.Theory.Comodule.html#Comodule
[FCM]: Cat.Theory.Comodule.html#Functoriality
[MCM]: Cat.Theory.Comodule.html#Morphism
[CMC]: Cat.Category.RComod.html#𝑹𝑪𝒐𝒎𝒐𝒅
[TCM]: Cat.Theory.PushforwardComodule.html#tautological_comodule
[PCM]: Cat.Theory.PushforwardComodule.html#pushforward_construction
[ICM]: Cat.Theory.PushforwardComodule.html#induced_morphism
[RCC]: Cat.Theory.RelativeComonadWithCut.html#RelativeComonadWithCut
[MRCC]: Cat.Theory.RelativeComonadWithCut.html#Morphism
[CRCC]: Cat.Category.RComonadWithCut.html#𝑹𝑪𝒐𝒎𝒐𝒏𝒂𝒅𝑾𝒊𝒕𝒉𝑪𝒖𝒕
[CCRCC]: Cat.Category.RComonad_RComonadWithCut.html
[PRCC]: Cat.Theory.PrecompositionWithProduct.html#PrecompositionWithProduct
[PCRCC]: Cat.Theory.PushforwardComodule.html#Commutes
[TM]: Cat.Category.TriMat.html#𝑻𝒓𝒊𝑴𝒂𝒕
[CS]: Cat.Category.Coinitiality.html#Coinitiality
