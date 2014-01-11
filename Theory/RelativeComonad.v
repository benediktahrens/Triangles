(**

   Benedikt Ahrens and Régis Spadotti
   
   Coinitial semantics for redecoration of triangular matrices
   
   http://arxiv.org/abs/1401.1053

*)

Require Import Theory.Category.
Require Import Theory.Functor.

Generalizable All Variables.

(*------------------------------------------------------------------------------
  -- ＲＥＬＡＴＩＶＥ  ＣＯＭＯＮＡＤ  ＤＥＦＩＮＩＴＩＯＮ
  ----------------------------------------------------------------------------*)

Structure RelativeComonad `(F : Functor 𝒞 𝒟) : Type := mkRelativeComonad
{ T              :> 𝒞 → 𝒟
; counit         : ∀ {X}, T X ⇒ F X
; cobind         : ∀ {X Y}, [ T X ⇒ F Y ⟶ T X ⇒ T Y ]
; cobind_counit  : ∀ {X}, cobind counit ≈ id[ T X ]
; counit_cobind  : ∀ {X Y} {f : T X ⇒ F Y}, counit ∘ cobind(f) ≈ f
; cobind_cobind : ∀ {X Y Z} {f : T X ⇒ F Y} {g : T Y ⇒ F Z}, cobind(g) ∘ cobind(f) ≈ cobind(g ∘ cobind(f)) }.

Arguments mkRelativeComonad {_ _ _ _ _ _} _ _ _.
Arguments counit            {_ _ _} _ {_}.
Arguments cobind            {_ _ _} _ {_ _}.
Arguments cobind_counit     {_ _ _} _ {_}.
Arguments counit_cobind     {_ _ _} _ {_ _ _}.
Arguments cobind_cobind    {_ _ _} _ {_ _ _ _ _}.

Notation "'counit[' X ]" := (counit _ (X := X)) (only parsing).
Notation "T '⋅counit'" := (counit T) (at level 0, only parsing).
Notation "T '⋅counit[' X ]" := (counit T (X := X)) (at level 0, only parsing).

Notation "T '⋅cobind'" := (cobind T) (at level 0, only parsing).

Notation make T counit cobind := (@mkRelativeComonad _ _ _ T counit cobind _ _ _) (only parsing).

(*------------------------------------------------------------------------------
  -- ＦＵＮＣＴＯＲＩＡＬＩＴＹ
  ----------------------------------------------------------------------------*)

Section Functoriality.

  Context `{F : Functor 𝒞 𝒟} (T : RelativeComonad F).

  Program Definition lift {A B} : [ A ⇒ B ⟶ T A ⇒ T B ] :=
    λ f ↦ T⋅cobind (F⋅f ∘ T⋅counit).
  Next Obligation.
    intros f g eq_fg. now rewrite eq_fg.
  Qed.

  Lemma lift_id : ∀ A, id[ T A ] ≈ lift id[ A ].
  Proof.
    intros A; simpl; unfold lift.
    rewrite <- identity, left_id, cobind_counit.
    reflexivity.
  Qed.

  Lemma lift_compose : ∀ A B C (f : A ⇒ B) (g : B ⇒ C), lift (g ∘ f) ≈ (lift g) ∘ (lift f).
  Proof.
    intros A B C g f; simpl; unfold lift.
    rewrite cobind_cobind,
            compose_assoc,
            counit_cobind,
            <- compose_assoc,
            <- map_compose.
    reflexivity.
  Qed.

  Definition Lift : Functor 𝒞 𝒟 := mkFunctor lift_id lift_compose.

End Functoriality.


(*------------------------------------------------------------------------------
  -- ＭＯＲＰＨＩＳＭ
  ----------------------------------------------------------------------------*)

Structure Morphism `{F : Functor 𝒞 𝒟} (T S : RelativeComonad F) : Type := mkMorphism
{ τ          :> ∀ C, T C ⇒ S C
; τ_counit   : ∀ {C}, T⋅counit[ C ] ≈ S⋅counit[ C ] ∘ τ(C)
; τ_commutes : ∀ {C D} {f : S C ⇒ F D}, τ(D) ∘ T⋅cobind (f ∘ τ(C)) ≈ S⋅cobind f ∘ τ(C) }.

Arguments mkMorphism {_ _ _ _ _ _} _ _.
Arguments τ          {_ _ _ _ _ _} _.
Arguments τ_counit   {_ _ _ _ _} _ {_}.
Arguments τ_commutes {_ _ _ _ _} _ {_ _ _}.

Module Morphism.

  Notation make τ := (@mkMorphism _ _ _ _ _ τ _ _) (only parsing).

  (* -- Ｉｄｅｎｔｉｔｙ  /  Ｃｏｍｐｏｓｉｔｉｏｎ                      -- *)
  Section id_composition.

    Context `{F : Functor 𝒞 𝒟}.

    Implicit Types (T S U : RelativeComonad F).

    Program Definition Hom T S : Setoid :=
      Setoid.make (Morphism T S) (λ f g ∙ ∀ x, f x ≈ g x).
    Next Obligation.
      constructor.
      - intros f x; reflexivity.
      - intros f g eq_fg x. symmetry. apply eq_fg.
      - intros f g h eq_fg eq_gh; etransitivity; eauto.
    Qed.

    Local Infix "⇒" := Hom.

    Program Definition id {S} : S ⇒ S :=
      make (λ C ∙ id[ S C ]).
    Next Obligation.
      now rewrite right_id.
    Qed.
    Next Obligation.
      rewrite left_id; now do 2 rewrite right_id.
    Qed.

    Program Definition compose {S T U} : [ T ⇒ U ⟶ S ⇒ T ⟶ S ⇒ U ] :=
      λ g f ↦₂ make (λ C ∙ g(C) ∘ f(C)).
    Next Obligation.
      rewrite <- compose_assoc; now do 2 rewrite <- τ_counit.
    Qed.
    Next Obligation.
      setoid_rewrite <- compose_assoc at 2.
      rewrite <- τ_commutes. rewrite compose_assoc.
      setoid_rewrite <- compose_assoc at 2. rewrite τ_commutes.
      rewrite <- compose_assoc. reflexivity.
    Qed.
    Next Obligation.
      intros f₁ f₂ eq_f₁f₂ g₁ g₂ eq_g₁g₂ x. simpl.
      apply Π₂.cong; [ apply eq_f₁f₂ | apply eq_g₁g₂ ].
    Qed.

  End id_composition.

End Morphism.
