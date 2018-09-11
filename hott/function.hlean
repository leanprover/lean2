/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Ported from Coq HoTT
Theorems about embeddings and surjections
-/

import hit.trunc types.equiv cubical.square types.nat

open equiv sigma sigma.ops eq trunc is_trunc pi is_equiv fiber prod pointed nat

variables {A B C : Type} (f f' : A → B) {b : B}

/- the image of a map is the (-1)-truncated fiber -/
definition image' [constructor] (f : A → B) (b : B) : Type := ∥ fiber f b ∥
definition is_prop_image' [instance] (f : A → B) (b : B) : is_prop (image' f b) := !is_trunc_trunc
definition image [constructor] (f : A → B) (b : B) : Prop := Prop.mk (image' f b) _

definition total_image {A B : Type} (f : A → B) : Type := sigma (image f)

/- properties of functions -/

definition is_embedding [class] (f : A → B) := Π(a a' : A), is_equiv (ap f : a = a' → f a = f a')

definition is_surjective [class] (f : A → B) := Π(b : B), image f b

definition is_split_surjective [class] (f : A → B) := Π(b : B), fiber f b

structure is_retraction [class] (f : A → B) :=
  (sect : B → A)
  (right_inverse : Π(b : B), f (sect b) = b)

structure is_section [class] (f : A → B) :=
  (retr : B → A)
  (left_inverse : Π(a : A), retr (f a) = a)

definition is_weakly_constant [class] (f : A → B) := Π(a a' : A), f a = f a'

structure is_constant [class] (f : A → B) :=
  (pt : B)
  (eq : Π(a : A), f a = pt)

definition merely_constant {A B : Type} (f : A → B) : Type :=
Σb, Πa, merely (f a = b)

structure is_conditionally_constant [class] (f : A → B) :=
  (g : ∥A∥ → B)
  (eq : Π(a : A), f a = g (tr a))

section image
protected definition image.mk [constructor] {f : A → B} {b : B} (a : A) (p : f a = b)
  : image f b :=
tr (fiber.mk a p)

protected definition image.rec [unfold 8] [recursor 8] {f : A → B} {b : B} {P : image' f b → Type}
  [H : Πv, is_prop (P v)] (H : Π(a : A) (p : f a = b), P (image.mk a p)) (v : image' f b) : P v :=
begin unfold [image'] at *, induction v with v, induction v with a p, exact H a p end

definition image.elim {A B : Type} {f : A → B} {C : Type} [is_prop C] {b : B}
  (H : image f b) (H' : ∀ (a : A), f a = b → C) : C :=
begin
  refine (trunc.elim _ H),
  intro H'', cases H'' with a Ha, exact H' a Ha
end

definition image.equiv_exists {A B : Type} {f : A → B} {b : B} : image f b ≃ ∃ a, f a = b :=
trunc_equiv_trunc _ (fiber.sigma_char _ _)

definition image_pathover {f : A → B} {x y : B} (p : x = y) (u : image f x) (v : image f y) :
  u =[p] v :=
!is_prop.elimo

definition total_image.rec [unfold 7]
  {A B : Type} {f : A → B} {C : total_image f → Type} [H : Πx, is_prop (C x)]
  (g : Πa, C ⟨f a, image.mk a idp⟩)
  (x : total_image f) : C x :=
begin
  induction x with b v,
  refine @image.rec _ _ _ _ _ (λv, H ⟨b, v⟩) _ v,
  intro a p,
  induction p, exact g a
end

/- total_image.elim_set is in hit.prop_trunc to avoid dependency cycle -/

end image

namespace function

  abbreviation sect          [unfold 4] := @is_retraction.sect
  abbreviation right_inverse [unfold 4] := @is_retraction.right_inverse
  abbreviation retr          [unfold 4] := @is_section.retr
  abbreviation left_inverse  [unfold 4] := @is_section.left_inverse

  definition is_equiv_ap_of_embedding [instance] [H : is_embedding f] (a a' : A)
    : is_equiv (ap f : a = a' → f a = f a') :=
  H a a'

  definition ap_inv_idp {a : A} {H : is_equiv (ap f : a = a → f a = f a)}
    : (ap f)⁻¹ᶠ idp = idp :> a = a :=
  !left_inv

  variable {f}
  definition is_injective_of_is_embedding [reducible] [H : is_embedding f] {a a' : A}
    : f a = f a' → a = a' :=
  (ap f)⁻¹

  definition is_embedding_of_is_injective [HA : is_set A] [HB : is_set B]
    (H : Π(a a' : A), f a = f a' → a = a') : is_embedding f :=
  begin
  intro a a',
  fapply adjointify,
    {exact (H a a')},
    {intro p, apply is_set.elim},
    {intro p, apply is_set.elim}
  end

  variable (f)

  definition is_prop_is_embedding [instance] : is_prop (is_embedding f) :=
  by unfold is_embedding; exact _

  definition is_embedding_equiv_is_injective [HA : is_set A] [HB : is_set B]
    : is_embedding f ≃ (Π(a a' : A), f a = f a' → a = a') :=
  begin
  fapply equiv.MK,
    { apply @is_injective_of_is_embedding},
    { apply is_embedding_of_is_injective},
    { intro H, apply is_prop.elim},
    { intro H, apply is_prop.elim, }
  end

  definition is_prop_fiber_of_is_embedding [H : is_embedding f] (b : B) :
    is_prop (fiber f b) :=
  begin
    apply is_prop.mk, intro v w,
    induction v with a p, induction w with a' q, induction q,
    fapply fiber_eq,
    { esimp, apply is_injective_of_is_embedding p},
    { esimp [is_injective_of_is_embedding], symmetry, apply right_inv}
  end

  definition is_prop_fun_of_is_embedding [H : is_embedding f] : is_trunc_fun -1 f :=
  is_prop_fiber_of_is_embedding f

  definition is_embedding_of_is_prop_fun [constructor] [H : is_trunc_fun -1 f] : is_embedding f :=
  begin
    intro a a', fapply adjointify,
    { intro p, exact ap point (@is_prop.elim (fiber f (f a')) _ (fiber.mk a p) (fiber.mk a' idp))},
    { intro p, rewrite [-ap_compose], esimp, apply ap_con_eq (@point_eq _ _ f (f a'))},
    { intro p, induction p, apply ap (ap point), apply is_prop_elim_self}
  end

  variable {f}
  definition is_surjective_rec_on {P : Type} (H : is_surjective f) (b : B) [Pt : is_prop P]
    (IH : fiber f b → P) : P :=
  trunc.rec_on (H b) IH
  variable (f)

  definition is_surjective_of_is_split_surjective [instance] [H : is_split_surjective f]
    : is_surjective f :=
  λb, tr (H b)

  definition is_prop_is_surjective [instance] : is_prop (is_surjective f) :=
  begin unfold is_surjective, exact _ end

  definition is_surjective_cancel_right {A B C : Type} (g : B → C) (f : A → B)
    [H : is_surjective (g ∘ f)] : is_surjective g :=
  begin
    intro c,
    induction H c with a p,
    exact tr (fiber.mk (f a) p)
  end

  definition is_contr_of_is_surjective (f : A → B) (H : is_surjective f) (HA : is_contr A)
    (HB : is_set B) : is_contr B :=
  is_contr.mk (f !center) begin intro b, induction H b, exact ap f !is_prop.elim ⬝ p end

  definition is_surjective_of_is_contr [constructor] (f : A → B) (a : A) (H : is_contr B) :
    is_surjective f :=
  λb, image.mk a !eq_of_is_contr

  definition is_weakly_constant_ap [instance] [H : is_weakly_constant f] (a a' : A) :
    is_weakly_constant (ap f : a = a' → f a = f a') :=
  take p q : a = a',
  have Π{b c : A} {r : b = c}, (H a b)⁻¹ ⬝ H a c = ap f r, from
    (λb c r, eq.rec_on r !con.left_inv),
  this⁻¹ ⬝ this

  definition is_constant_ap [unfold 4] [instance] [H : is_constant f] (a a' : A)
    : is_constant (ap f : a = a' → f a = f a') :=
  begin
    induction H with b q,
    fapply is_constant.mk,
    { exact q a ⬝ (q a')⁻¹},
    { intro p, induction p, exact !con.right_inv⁻¹}
  end

  definition is_contr_is_retraction [instance] [H : is_equiv f] : is_contr (is_retraction f) :=
  begin
    have H2 : (Σ(g : B → A), Πb, f (g b) = b) ≃ is_retraction f,
    begin
      fapply equiv.MK,
        {intro x, induction x with g p, constructor, exact p},
        {intro h, induction h, apply sigma.mk, assumption},
        {intro h, induction h, reflexivity},
        {intro x, induction x, reflexivity},
    end,
    apply is_trunc_equiv_closed, exact H2,
    apply is_equiv.is_contr_right_inverse
  end

  definition is_contr_is_section [instance] [H : is_equiv f] : is_contr (is_section f) :=
  begin
    have H2 : (Σ(g : B → A), Πa, g (f a) = a) ≃ is_section f,
    begin
      fapply equiv.MK,
        {intro x, induction x with g p, constructor, exact p},
        {intro h, induction h, apply sigma.mk, assumption},
        {intro h, induction h, reflexivity},
        {intro x, induction x, reflexivity},
    end,
    apply is_trunc_equiv_closed, exact H2,
    fapply is_trunc_equiv_closed,
      {apply sigma_equiv_sigma_right, intro g, apply eq_equiv_homotopy},
    fapply is_trunc_equiv_closed,
      {apply fiber.sigma_char},
    fapply is_contr_fiber_of_is_equiv,
    exact to_is_equiv (arrow_equiv_arrow_left_rev A (equiv.mk f H)),
  end

  definition is_embedding_of_is_equiv [instance] [H : is_equiv f] : is_embedding f :=
  λa a', _

  definition is_equiv_of_is_surjective_of_is_embedding
    [H : is_embedding f] [H' : is_surjective f] : is_equiv f :=
  @is_equiv_of_is_contr_fun _ _ _
    (λb, is_surjective_rec_on H' b
      (λa, is_contr.mk a
        (λa',
          fiber_eq ((ap f)⁻¹ ((point_eq a) ⬝ (point_eq a')⁻¹))
                   (by rewrite (right_inv (ap f)); rewrite inv_con_cancel_right))))

  definition is_split_surjective_of_is_retraction [H : is_retraction f] : is_split_surjective f :=
  λb, fiber.mk (sect f b) (right_inverse f b)

  definition is_constant_compose_point [constructor] [instance] (b : B)
    : is_constant (f ∘ point : fiber f b → B) :=
  is_constant.mk b (λv, by induction v with a p;exact p)

  definition is_embedding_of_is_prop_fiber [H : Π(b : B), is_prop (fiber f b)] : is_embedding f :=
  is_embedding_of_is_prop_fun _

  definition is_retraction_of_is_equiv [instance] [H : is_equiv f] : is_retraction f :=
  is_retraction.mk f⁻¹ (right_inv f)

  definition is_section_of_is_equiv [instance] [H : is_equiv f] : is_section f :=
  is_section.mk f⁻¹ (left_inv f)

  definition is_equiv_of_is_section_of_is_retraction [H1 : is_retraction f] [H2 : is_section f]
    : is_equiv f :=
  let g := sect f in let h := retr f in
  adjointify f
             g
             (right_inverse f)
             (λa, calc
                    g (f a) = h (f (g (f a))) : left_inverse
                    ... = h (f a) : right_inverse f
                    ... = a : left_inverse)

  section
    local attribute is_equiv_of_is_section_of_is_retraction [instance] [priority 10000]
    local attribute trunctype.struct [instance] [priority 1] -- remove after #842 is closed
    variable (f)
    definition is_prop_is_retraction_prod_is_section : is_prop (is_retraction f × is_section f) :=
    begin
      apply is_prop_of_imp_is_contr, intro H, induction H with H1 H2,
      exact _,
    end
  end

  definition is_retraction_trunc_functor [instance] (r : A → B) [H : is_retraction r]
    (n : trunc_index) : is_retraction (trunc_functor n r) :=
  is_retraction.mk
    (trunc_functor n (sect r))
    (λb,
      ((trunc_functor_compose n (sect r) r) b)⁻¹
      ⬝ trunc_homotopy n (right_inverse r) b
      ⬝ trunc_functor_id n B b)

  -- Lemma 3.11.7
  definition is_contr_retract (r : A → B) [H : is_retraction r] : is_contr A → is_contr B :=
  begin
    intro CA,
    apply is_contr.mk (r (center A)),
    intro b,
    exact ap r (center_eq (is_retraction.sect r b)) ⬝ (is_retraction.right_inverse r b)
  end

  local attribute is_prop_is_retraction_prod_is_section [instance]
  definition is_retraction_prod_is_section_equiv_is_equiv [constructor]
    : (is_retraction f × is_section f) ≃ is_equiv f :=
  begin
    apply equiv_of_is_prop,
    intro H, induction H, apply is_equiv_of_is_section_of_is_retraction,
    intro H, split, repeat exact _
  end

  definition is_retraction_equiv_is_split_surjective :
    is_retraction f ≃ is_split_surjective f :=
  begin
    fapply equiv.MK,
    { intro H, induction H with g p, intro b, constructor, exact p b},
    { intro H, constructor, intro b, exact point_eq (H b)},
    { intro H, esimp, apply eq_of_homotopy, intro b, esimp, induction H b, reflexivity},
    { intro H, induction H with g p, reflexivity},
  end

  definition is_embedding_compose (g : B → C) (f : A → B)
    (H₁ : is_embedding g) (H₂ : is_embedding f) : is_embedding (g ∘ f) :=
  begin
    intros, apply is_equiv.homotopy_closed (ap g ∘ ap f),
    { symmetry, exact ap_compose g f },
    { exact is_equiv_compose _ _ _ _ }
  end

  definition is_surjective_compose (g : B → C) (f : A → B)
    (H₁ : is_surjective g) (H₂ : is_surjective f) : is_surjective (g ∘ f) :=
  begin
    intro c, induction H₁ c with b p, induction H₂ b with a q,
    exact image.mk a (ap g q ⬝ p)
  end

  definition is_split_surjective_compose (g : B → C) (f : A → B)
    (H₁ : is_split_surjective g) (H₂ : is_split_surjective f) : is_split_surjective (g ∘ f) :=
  begin
    intro c, induction H₁ c with b p, induction H₂ b with a q,
    exact fiber.mk a (ap g q ⬝ p)
  end

  definition is_injective_compose (g : B → C) (f : A → B)
    (H₁ : Π⦃b b'⦄, g b = g b' → b = b') (H₂ : Π⦃a a'⦄, f a = f a' → a = a')
    ⦃a a' : A⦄ (p : g (f a) = g (f a')) : a = a' :=
  H₂ (H₁ p)

  definition is_embedding_pr1 [instance] [constructor] {A : Type} (B : A → Type) [H : Π a, is_prop (B a)]
      : is_embedding (@pr1 A B) :=
  λv v', to_is_equiv (sigma_eq_equiv v v' ⬝e !sigma_equiv_of_is_contr_right)

  variables {f f'}
  definition is_embedding_homotopy_closed (p : f ~ f') (H : is_embedding f) : is_embedding f' :=
  begin
    intro a a', fapply is_equiv_of_equiv_of_homotopy,
    exact equiv.mk (ap f) _ ⬝e equiv_eq_closed_left _ (p a) ⬝e equiv_eq_closed_right _ (p a'),
    intro q, esimp, exact (eq_bot_of_square (transpose (natural_square p q)))⁻¹
  end

  definition is_embedding_homotopy_closed_rev (p : f' ~ f) (H : is_embedding f) : is_embedding f' :=
  is_embedding_homotopy_closed p⁻¹ʰᵗʸ H

  definition is_surjective_homotopy_closed (p : f ~ f') (H : is_surjective f) : is_surjective f' :=
  begin
    intro b, induction H b with a q,
    exact image.mk a ((p a)⁻¹ ⬝ q)
  end

  definition is_surjective_homotopy_closed_rev (p : f' ~ f) (H : is_surjective f) :
    is_surjective f' :=
  is_surjective_homotopy_closed p⁻¹ʰᵗʸ H

  definition is_surjective_factor {g : B → C} (f : A → B) (h : A → C) (H : g ∘ f ~ h) :
    is_surjective h → is_surjective g :=
  begin
    induction H using homotopy.rec_on_idp,
    intro S,
    intro c,
    note p := S c,
    induction p,
    apply tr,
    fapply fiber.mk,
    exact f a,
    exact p
  end

  definition is_equiv_ap1_gen_of_is_embedding {A B : Type} (f : A → B) [is_embedding f]
    {a a' : A} {b b' : B} (q : f a = b) (q' : f a' = b') : is_equiv (ap1_gen f q q') :=
  begin
    induction q, induction q',
    exact is_equiv.homotopy_closed _ (ap1_gen_idp_left f)⁻¹ʰᵗʸ _,
  end

  definition is_equiv_ap1_of_is_embedding {A B : Type*} (f : A →* B) [is_embedding f] :
    is_equiv (Ω→ f) :=
  is_equiv_ap1_gen_of_is_embedding f (respect_pt f) (respect_pt f)

  definition loop_pequiv_loop_of_is_embedding [constructor] {A B : Type*} (f : A →* B)
    [is_embedding f] : Ω A ≃* Ω B :=
  pequiv_of_pmap (Ω→ f) (is_equiv_ap1_of_is_embedding f)

  definition loopn_pequiv_loopn_of_is_embedding [constructor] (n : ℕ) [H : is_succ n]
    {A B : Type*} (f : A →* B) [is_embedding f] : Ω[n] A ≃* Ω[n] B :=
  begin
    induction H with n,
    exact !loopn_succ_in ⬝e*
      loopn_pequiv_loopn n (loop_pequiv_loop_of_is_embedding f) ⬝e*
      !loopn_succ_in⁻¹ᵉ*
  end

  definition is_contr_of_is_embedding (f : A → B) (H : is_embedding f) (HB : is_prop B)
    (a₀ : A) : is_contr A :=
  is_contr.mk a₀ (λa, is_injective_of_is_embedding (is_prop.elim (f a₀) (f a)))

  definition is_embedding_of_square {A B C D : Type} {f : A → B} {g : C → D} (h : A ≃ C)
    (k : B ≃ D) (s : k ∘ f ~ g ∘ h) (Hf : is_embedding f) : is_embedding g :=
  begin
    apply is_embedding_homotopy_closed, exact inv_homotopy_of_homotopy_pre _ _ _ s,
    apply is_embedding_compose, apply is_embedding_compose,
    apply is_embedding_of_is_equiv, exact Hf, apply is_embedding_of_is_equiv
  end

  definition is_embedding_of_square_rev {A B C D : Type} {f : A → B} {g : C → D} (h : A ≃ C)
    (k : B ≃ D) (s : k ∘ f ~ g ∘ h) (Hg : is_embedding g) : is_embedding f :=
  is_embedding_of_square h⁻¹ᵉ k⁻¹ᵉ s⁻¹ʰᵗʸᵛ Hg

  definition is_embedding_factor [is_set A] [is_set B] (g : B → C) (h : A → C) (H : g ∘ f ~ h) :
    is_embedding h → is_embedding f :=
  begin
    induction H using homotopy.rec_on_idp,
    intro E,
    fapply is_embedding_of_is_injective,
    intro x y p,
    fapply @is_injective_of_is_embedding _ _ _ E _ _ (ap g p)
  end

  /-
    The definitions
      is_surjective_of_is_equiv
      is_equiv_equiv_is_embedding_times_is_surjective
    are in types.trunc

    See types.arrow_2 for retractions
  -/

end function
