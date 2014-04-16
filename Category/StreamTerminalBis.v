Require Import Category.Setoids.
Require Import Category.Sets.
Require Import Category.Sets_Setoids.
Require Import Category.RComod.
Require Import Category.RComonad.
Require Import Category.Stream.
Require Import Theory.Category.
Require Import Theory.InitialTerminal.
Require Import Theory.Functor.
Require Import Theory.RelativeComonad.
Require Import Theory.Comodule.
Require Import Theory.Product.
Require Import Theory.PrecompositionWithProduct.
Require Import Theory.PushforwardComodule.

Generalizable All Variables.


Module Type StreamAxioms.

  (** Stream and destructors **)
  Axiom Stream : 𝑺𝒆𝒕 → 𝑺𝒆𝒕.
  Axiom head : ∀ {A}, Stream A ⇒ A.
  Axiom tail : ∀ {A}, Stream A ⇒ Stream A.

  (** Corecursor on Stream **)
  Axiom corec : ∀ {A T : 𝑺𝒆𝒕}, (T ⇒ A) → (T ⇒ T) → T ⇒ Stream A.
  Axiom head_corec : ∀ {A T : 𝑺𝒆𝒕} {hd : T ⇒ A} {tl : T ⇒ T} {t}, head (corec hd tl t) = hd t.
  Axiom tail_corec : ∀ {A T : 𝑺𝒆𝒕} {hd : T ⇒ A} {tl : T ⇒ T} {t}, tail (corec hd tl t) = corec hd tl (tl t).

  (** Equivalence relation on streams **)
  Axiom bisim : ∀ {A}, Stream A → Stream A → Prop.
  Infix "∼" := bisim (at level 70).

  Axiom bisim_head : ∀ {A} {s₁ s₂ : Stream A}, s₁ ∼ s₂ → head s₁ = head s₂.
  Axiom bisim_tail : ∀ {A} {s₁ s₂ : Stream A}, s₁ ∼ s₂ → tail s₁ ∼ tail s₂.
  Notation "∼-head" := bisim_head (only parsing).
  Notation "∼-tail" := bisim_tail (only parsing).

  Axiom bisim_intro : ∀ {A}
                        (R : Stream A → Stream A → Prop)
                        (R_head : ∀ {s₁ s₂ : Stream A}, R s₁ s₂ → head s₁ = head s₂)
                        (R_tail : ∀ {s₁ s₂ : Stream A}, R s₁ s₂ → R (tail s₁) (tail s₂)),
                        ∀ {s₁ s₂ : Stream A}, R s₁ s₂ → s₁ ∼ s₂.

End StreamAxioms.

Module StreamInstance : StreamAxioms.

  CoInductive Stream_ A : Type :=
    Cons : A → Stream_ A → Stream_ A.

  Arguments Cons {_} _ _.

  Notation "_∷_" := Cons.
  Notation "x ∷ xs" := (Cons x xs) (at level 60, right associativity).

  Definition Stream : 𝑺𝒆𝒕 → 𝑺𝒆𝒕 := Stream_.
  Definition head {A} : Stream A ⇒ A := λ s ∙ let '(x ∷ _) := s in x.
  Definition tail {A} : Stream A ⇒ Stream A := λ s ∙ let '(_ ∷ xs) := s in xs.

  CoFixpoint corec {A T : 𝑺𝒆𝒕} (hd : T ⇒ A) (tl : T ⇒ T) : T ⇒ Stream A :=
    λ t ∙ hd t ∷ corec hd tl (tl t).

  Lemma head_corec : ∀ {A T : 𝑺𝒆𝒕} {hd : T ⇒ A} {tl : T ⇒ T} {t}, head (corec hd tl t) = hd t.
  Proof.
    reflexivity.
  Qed.

  Lemma tail_corec : ∀ {A T : 𝑺𝒆𝒕} {hd : T ⇒ A} {tl : T ⇒ T} {t}, tail (corec hd tl t) = corec hd tl (tl t).
  Proof.
    reflexivity.
  Qed.

  (** Equivalence relation on streams **)
  Reserved Notation "x ∼ y" (at level 70, right associativity).

  CoInductive bisim_ {A} : Stream A → Stream A → Prop :=
  | bintro : ∀ {s₁ s₂ : Stream A}, head s₁ = head s₂ → tail s₁ ∼ tail s₂ → s₁ ∼ s₂
  where "s₁ ∼ s₂" := (@bisim_ _ s₁ s₂).

  Definition bisim {A} := @bisim_ A.

  Lemma bisim_head : ∀ {A} {s₁ s₂ : Stream A}, s₁ ∼ s₂ → head s₁ = head s₂.
  Proof.
    intros. now destruct H.
  Qed.
  Lemma bisim_tail : ∀ {A} {s₁ s₂ : Stream A}, s₁ ∼ s₂ → tail s₁ ∼ tail s₂.
  Proof.
    intros. now destruct H.
  Qed.

  Lemma bisim_intro : ∀ {A}
                        (R : Stream A → Stream A → Prop)
                        (R_head : ∀ {s₁ s₂ : Stream A}, R s₁ s₂ → head s₁ = head s₂)
                        (R_tail : ∀ {s₁ s₂ : Stream A}, R s₁ s₂ → R (tail s₁) (tail s₂)),
                        ∀ {s₁ s₂ : Stream A}, R s₁ s₂ → s₁ ∼ s₂.
  Proof.
    cofix Hc; constructor; intros.
    - now apply R_head.
    - eapply Hc; eauto. now apply R_tail.
  Qed.

End StreamInstance.

Ltac clean_hyps := repeat match goal with H : _ |- _ => clear H end.

Module StreamTerminal (Import Ax : StreamAxioms).

  Lemma bisim_refl : ∀ {A} {s : Stream A}, s ∼ s.
  Proof.
    intros. apply bisim_intro with (R := λ s₁ s₂ ∙ s₁ = s₂); [clean_hyps; intros..|auto].
    - subst; reflexivity.
    - subst; reflexivity.
  Qed.

  Lemma bisim_sym : ∀ {A} {s₁ s₂ : Stream A}, s₁ ∼ s₂ → s₂ ∼ s₁.
  Proof.
    intros.
    apply bisim_intro with (R := λ s₁ s₂ ∙ s₂ ∼ s₁); [clean_hyps; intros..|auto].
    - symmetry; now apply bisim_head.
    - now apply bisim_tail.
  Qed.

  Lemma bisim_trans : ∀ {A} {s₁ s₂ s₃ : Stream A}, s₁ ∼ s₂ → s₂ ∼ s₃ → s₁ ∼ s₃.
  Proof.
    intros.
    apply bisim_intro with (R := λ s₁ s₃ ∙ ∃ s₂, s₁ ∼ s₂ ∧ s₂ ∼ s₃);
    [clean_hyps; intros.. | eauto].
    - destruct H as (? & ? & ?).
      etransitivity. eapply bisim_head; eauto.
      now apply bisim_head.
    - destruct H as (? & ? & ?).
      eexists; split; eapply bisim_tail; eauto.
  Qed.

  Instance bisim_equiv : ∀ {A}, Equivalence (@bisim A).
  Proof.
    constructor; repeat intro.
    - now apply bisim_refl.
    - now apply bisim_sym.
    - eapply bisim_trans; eauto.
  Qed.

  Lemma eq_bisim : ∀ {A} {s₁ s₂ : Stream A}, s₁ = s₂ → s₁ ∼ s₂.
  Proof.
    intros. now rewrite H.
  Qed.

  Lemma head_cong : ∀ {A} {s₁ s₂ : Stream A}, s₁ ∼ s₂ → head s₁ = head s₂.
  Proof.
    intros A s₁ s₂ eq_s₁s₂. now apply bisim_head.
  Qed.

  Lemma tail_cong : ∀ {A} {s₁ s₂ : Stream A}, s₁ ∼ s₂ → tail s₁ ∼ tail s₂.
  Proof.
    intros A s₁ s₂ eq_s₁s₂. now apply bisim_tail.
  Qed.

  Program Definition STREAM (A : Type) : Setoids.Obj :=
    Setoids.make ⦃ Carrier ≔ Stream A ; Equiv ≔ bisim ⦄.

  Program Definition 𝒉𝒆𝒂𝒅 {A} : STREAM A ⇒ 𝑬𝑸 A := Setoids.Morphism.make head.
  Next Obligation.
    now apply head_cong.
  Qed.

  Program Definition 𝒕𝒂𝒊𝒍 {A} : STREAM A ⇒ STREAM A := Setoids.Morphism.make tail.
  Next Obligation.
    now apply tail_cong.
  Qed.

  Definition redec {A B : 𝑺𝒆𝒕} (f : Stream A ⇒ B) : Stream A ⇒ Stream B :=
    corec f tail.

  Obligation Tactic := idtac.
  Program Definition 𝑺𝒕𝒓 : ‵ 𝑹𝑪𝒐𝒎𝒐𝒏𝒂𝒅 𝑬𝑸 ′ :=
    RelativeComonad.make ⦃ T ≔ STREAM
                           ; counit ≔ λ X ∙ 𝒉𝒆𝒂𝒅
                           ; cobind ≔ λ X Y ∙ λ f ↦ Setoids.Morphism.make (redec f) ⦄.
  Next Obligation.
    intros.
    apply bisim_intro with (λ s₁ s₂ ∙ ∃ x y, x ∼ y ∧ s₁ = redec f x ∧ s₂ = redec f y); [clean_hyps; intros..|eauto].
    - destruct H as (x & y & eq_xy & -> & ->).
      unfold redec. repeat rewrite head_corec.
      now rewrite eq_xy.
    - destruct H as (x & y & eq_xy & -> & ->).
      exists (tail x). exists (tail y).
      split; [|split].
      + now apply bisim_tail.
      + unfold redec at 1. rewrite tail_corec. reflexivity.
      + unfold redec at 1. rewrite tail_corec. reflexivity.
  Qed.
  Next Obligation.
    intros X Y f g eq_fg x y eq_xy. simpl.
    apply bisim_intro with (λ s₁ s₂ ∙ ∃ x y, x ∼ y ∧ s₁ = redec f x ∧ s₂ = redec g y); [intros..|eauto].
    - destruct H as (x' & y' & eq_xy' & -> & ->).
      unfold redec; repeat rewrite head_corec.
      etransitivity. eapply (Setoids.cong f). apply eq_xy'.
      now apply eq_fg.
    - destruct H as (x' & y' & eq_xy' & -> & ->).
      exists (tail x'). exists (tail y').
      split; [|split].
      + now apply bisim_tail.
      + unfold redec at 1. rewrite tail_corec. reflexivity.
      + unfold redec at 1. rewrite tail_corec. reflexivity.
  Qed.
  Next Obligation.
    simpl. intros.
    apply bisim_intro with (λ s₁ s₂ ∙ ∃ x y, x ∼ y ∧ s₁ = redec head x ∧ s₂ = y); [clean_hyps; intros..|eauto].
    - destruct H as (x & y & eq_xy & -> & ->).
      unfold redec; rewrite head_corec; now apply head_cong.
    - destruct H as (x & y & eq_xy & -> & ->).
      exists (tail x). exists (tail y).
      split; [|split].
      + now apply bisim_tail.
      + unfold redec at 1. rewrite tail_corec. reflexivity.
      + reflexivity.
  Qed.
  Next Obligation.
    repeat intro. rewrite H. simpl. unfold redec. now rewrite head_corec.
  Qed.
  Next Obligation.
    intros X Y Z f g x y eq_xy. rewrite <- eq_xy. clear y eq_xy. simpl.
    apply bisim_intro with (λ s₁ s₂ ∙ ∃ x, s₁ = redec g (redec f x) ∧ s₂ = redec (λ y ∙ g (redec f y)) x);
    [clean_hyps; intros..|eauto].
    - destruct H as (x & -> & ->).
      unfold redec. repeat rewrite head_corec. reflexivity.
    - destruct H as (x & -> & ->).
      exists (tail x). split.
      + unfold redec. now do 2 rewrite tail_corec.
      + unfold redec. now rewrite tail_corec.
  Qed.

  Program Definition 𝑻𝒂𝒊𝒍 : ‵ [𝑺𝒕𝒓] ⇒ [𝑺𝒕𝒓] ′ :=
    Comodule.make ⦃ α ≔ λ A ∙ Setoids.Morphism.make 𝒕𝒂𝒊𝒍 ⦄.
  Next Obligation.
    intros A x y eq_xy; now rewrite eq_xy.
  Qed.
  Next Obligation.
    intros C D f x y eq_xy. rewrite eq_xy. apply eq_bisim. simpl. unfold redec. now rewrite tail_corec.
  Qed.

  Program Definition 𝑺𝑻𝑹 : ‵ 𝑺𝒕𝒓𝒆𝒂𝒎 ′ :=
    Stream.make ⦃ T ≔ 𝑺𝒕𝒓 ; tail ≔ 𝑻𝒂𝒊𝒍 ⦄.

  Section Defs.

    Variable (Tr : 𝑺𝒕𝒓𝒆𝒂𝒎).

    Notation T                  := (Stream.T Tr).
    Notation "'T⋅tail'"         := (Stream.tail Tr _).
    Notation "'T⋅tail[' A ]"    := (Stream.tail Tr A) (only parsing).
    Notation STR                := (Stream.T 𝑺𝑻𝑹).
    Notation "'STR⋅tail'"       := (Stream.tail 𝑺𝑻𝑹 _).
    Notation "'STR⋅tail[' A ]"  := (Stream.tail 𝑺𝑻𝑹 A) (only parsing).

    Local Notation "a ∼ b" := (SEquiv a b).

    Definition tau {A} : T A → STR A := corec T⋅counit T⋅tail.

    Lemma head_tau : ∀ A (t : T A), STR⋅counit (tau t) = T⋅counit t.
    Proof.
      intros. unfold tau. simpl. now rewrite head_corec.
    Qed.

    Lemma tail_tau : ∀ A (t : T A), STR⋅tail (tau t) = tau (T⋅tail t).
    Proof.
      intros. unfold tau. simpl. now rewrite tail_corec.
    Qed.

    Lemma tau_cong : ∀ A (x y : T A), x ∼ y → tau x ∼ tau y.
    Proof.
      intros.
      apply bisim_intro with (λ s₁ s₂ ∙ ∃ x y, x ∼ y ∧ s₁ = tau x ∧ s₂ = tau y);
      [clean_hyps; intros..|eauto].
      - destruct H as (x & y & eq_xy & -> & ->).
        unfold tau. repeat rewrite head_corec. now rewrite eq_xy.
      - destruct H as (x & y & eq_xy & -> & ->).
        exists (T⋅tail x). exists (T⋅tail y). split; [|split].
        + now rewrite eq_xy.
        + unfold tau. now rewrite tail_corec.
        + unfold tau. now rewrite tail_corec.
    Qed.

    Program Definition Tau {A} : T A ⇒ STR A :=
      Setoids.Morphism.make tau.
    Next Obligation.
      intros. now apply tau_cong.
    Qed.

    Lemma tau_counit : ∀ A (t t' : T A), t ∼ t' → T⋅counit t ∼ STR⋅counit (tau t').
    Proof.
      intros A t t' eq_tt'. rewrite eq_tt'. simpl. unfold tau. now rewrite head_corec.
    Qed.

    Lemma tau_cobind : ∀ A B (f : STR A ⇒ 𝑬𝑸 B) x y, x ∼ y → Tau (T⋅cobind (f ∘ Tau) x) ∼ STR⋅cobind f (Tau y).
    Proof.
      intros A B f x y eq_xy. rewrite <- eq_xy. clear y eq_xy.
      apply bisim_intro with (λ s₁ s₂ ∙ ∃ x, s₁ ∼ Tau (T⋅cobind (f ∘ Tau) x) ∧ s₂ ∼ STR⋅cobind f (Tau x));
      [clean_hyps;intros..|eauto].
      - destruct H as (x & ? & ?).
        etransitivity. eapply head_cong. apply H.
        symmetry; etransitivity. eapply head_cong; apply H0.
        simpl. unfold tau, redec. repeat rewrite head_corec.
        symmetry. etransitivity. apply (counit_cobind T). reflexivity.
        reflexivity.
      - destruct H as (x & ? & ?).
        exists (T⋅tail x). split.
        etransitivity. eapply tail_cong. apply H.
        simpl. unfold tau. repeat rewrite tail_corec.
        apply tau_cong. etransitivity. apply (α_commutes (Stream.tail Tr)). reflexivity.
        simpl. reflexivity.
        etransitivity. eapply tail_cong. apply H0.
        simpl. unfold tau, redec. repeat rewrite tail_corec. reflexivity.
      - exists x; split; reflexivity.
    Qed.

  End Defs.

  (** printing τ #◯# *)

  (** ◯ is a morphism of triangles **)
  Program Definition τ (T : 𝑺𝒕𝒓𝒆𝒂𝒎) : T ⇒ 𝑺𝑻𝑹 :=
    Stream.make ⦃ τ ≔ RelativeComonad.make ⦃ τ ≔ λ A ∙ Tau T ⦄ ⦄.
  (** τ-counit **)
  Next Obligation.
    repeat intro. now apply tau_counit.
  Qed.
  (** τ-cobind **)
  Next Obligation.
    repeat intro. now apply tau_cobind.
  Qed.
  (** τ-commutes **)
  Next Obligation.
    repeat intro. rewrite H. simpl. unfold tau. repeat rewrite tail_corec. reflexivity.
  Qed.

  (* begin hide *)
  Local Notation "⟨ f ⟩" := (RelativeComonad.τ (m := Stream.τ f)) (only parsing).
  (* end hide *)

  (** 𝑺𝑻𝑹 is a terminal object **)
  Program Definition Coinitiality : Terminal 𝑺𝒕𝒓𝒆𝒂𝒎 :=
    Terminal.make  ⦃ one  ≔ 𝑺𝑻𝑹
                   ; top  ≔ τ ⦄.
  Next Obligation.
    intros A f X x y eq_xy. rewrite <- eq_xy. clear y eq_xy. simpl.
    apply bisim_intro with (λ s₁ s₂ ∙ ∃ x, s₁ ∼ ⟨f⟩ _ x ∧ s₂ ∼ tau A x); [clean_hyps; intros..|].
    - destruct H as (? & ? & ?).
      etransitivity. eapply head_cong. apply H.
      symmetry; etransitivity. eapply head_cong. apply H0.
      unfold tau. rewrite head_corec. symmetry. etransitivity. symmetry. apply (τ_counit (Stream.τ f)).
      reflexivity. reflexivity.
    - destruct H as (? & ? & ?).
      exists (Stream.tail A _ x). split.
      + etransitivity. eapply tail_cong. apply H.
        etransitivity. symmetry. eapply (Stream.τ_commutes f). reflexivity.
        reflexivity.
      + etransitivity. eapply tail_cong. apply H0.
        unfold tau. rewrite tail_corec. reflexivity.
    - exists x. split; reflexivity.
  Qed.

End StreamTerminal.

Module Terminality := StreamTerminal StreamInstance.