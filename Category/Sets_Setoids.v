(*

   Benedikt Ahrens and Régis Spadotti
   
   Coinitial semantics for redecoration of triangular matrices
   
   http://arxiv.org/abs/1401.1053

*)

(* 

  Content of this file:
  
  definition of the functor [EQ] from sets to setoids, proof that it is strong monoidal

*)

Require Import Category.Sets.
Require Import Category.Setoids.
Require Import Theory.Category.
Require Import Theory.Functor.
Require Import Theory.Product.
Require Import Theory.Isomorphism.
Require Import Theory.CartesianStrongMonoidal.

(*------------------------------------------------------------------------------
  -- ＦＵＮＣＴＯＲ  ＥＱ
  ----------------------------------------------------------------------------*)
(** * Functor 𝑬𝑸 : 𝑺𝒆𝒕 → 𝑺𝒆𝒕𝒐𝒊𝒅 **)

(** ** Definition **)

Program Definition F : 𝑺𝒆𝒕 → 𝑺𝒆𝒕𝒐𝒊𝒅 := λ T ∙ Setoids.make   ⦃ Carrier  ≔ T
                                                            ; Equiv    ≔ eq ⦄.

Program Definition map {A B} : [ A ⇒ B ⟶ F A ⇒ F B ] :=
  λ f ↦ Setoids.Morphism.make f.
Next Obligation.
  intros f g eq_fg x y eq_xy; simpl.
  now rewrite eq_xy.
Qed.

Definition id A : id[ F A ] ≈ map id[ A ].
Proof.
  intros x y eq_xy; now rewrite eq_xy.
Qed.

Definition map_compose A B C (f : A ⇒ B) (g : B ⇒ C) : map (g ∘ f) ≈ (map g) ∘ (map f).
Proof.
  intros x y eq_xy. now rewrite eq_xy.
Qed.

Definition 𝑬𝑸 : Functor 𝑺𝒆𝒕 𝑺𝒆𝒕𝒐𝒊𝒅 := mkFunctor id map_compose.


(*------------------------------------------------------------------------------
  -- ＥＱ  ＩＳ  ＳＴＲＯＮＧ  ＭＯＮＯＩＤＡＬ
  ----------------------------------------------------------------------------*)
(** ** 𝑬𝑸 is strong monoidal **)

Program Instance 𝑬𝑸_SM : CartesianStrongMonoidal 𝑬𝑸 :=
  CartesianStrongMonoidal.make ⦃ φ ≔ λ A B ∙ Setoids.Morphism.make (λ x ∙ x) ⦄.
Next Obligation.
  now f_equal.
Qed.
Next Obligation.
  constructor.
  - (* iso_left *)
    intros f g eq_fg. exact eq_fg.
  - (* iso_right *)
    intros f g eq_fg. simpl in *. destruct f. auto.
Qed.

(*------------------------------------------------------------------------------
  -- ＦＵＮＣＴＯＲ  ＥＱ-×
  ----------------------------------------------------------------------------*)
(** * Functor 𝑬𝑸-× : 𝑺𝒆𝒕 × 𝑺𝒆𝒕 → 𝑺𝒆𝒕𝒐𝒊𝒅 **)

(** ** Definition **)


Program Definition 𝑬𝑸_prod : Functor (𝑺𝒆𝒕 𝘅 𝑺𝒆𝒕) 𝑺𝒆𝒕𝒐𝒊𝒅 :=
  Functor.make ⦃ F ≔ λ A ∙ Setoids.make ⦃ Carrier ≔ fst A ⟨×⟩ snd A
                                        ; Equiv   ≔ eq ⦄
               ; map ≔ λ A B ∙ λ f ↦ Setoids.Morphism.make (λ x ∙ (fst f (fst x) , snd f (snd x))) ⦄.
Next Obligation.
  eauto with typeclass_instances.
Qed.
Next Obligation.
  intros [? ?] [? ?] [? ?] [? ?] [? ?] eq. injection eq; intros.
  simpl in *; f_equal; congruence.
Qed.

Notation "𝑬𝑸-𝘅" := 𝑬𝑸_prod.
