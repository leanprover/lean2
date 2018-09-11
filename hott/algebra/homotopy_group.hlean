/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

homotopy groups of a pointed space
-/

import .trunc_group types.trunc .group_theory types.nat.hott

open nat eq pointed trunc is_trunc algebra group function equiv unit is_equiv nat

/- todo: prove more properties of homotopy groups using gtrunc and agtrunc -/

namespace eq

  definition homotopy_group [reducible] [constructor] (n : ℕ) (A : Type*) : Set* :=
  ptrunc 0 (Ω[n] A)

  notation `π[`:95  n:0 `]`:0 := homotopy_group n

  section
  local attribute inf_group_loopn [instance]
  definition group_homotopy_group [instance] [constructor] [reducible] (n : ℕ) [is_succ n]
    (A : Type*) : group (π[n] A) :=
  group_trunc (Ω[n] A)
  end

  definition group_homotopy_group2 [instance] (k : ℕ) (A : Type*) :
    group (carrier (ptrunctype.to_pType (π[k + 1] A))) :=
  group_homotopy_group (k+1) A

  section
  local attribute ab_inf_group_loopn [instance]
  definition ab_group_homotopy_group [constructor] [reducible] (n : ℕ) [is_at_least_two n]
    (A : Type*) : ab_group (π[n] A) :=
  ab_group_trunc (Ω[n] A)
  end

  local attribute ab_group_homotopy_group [instance]

  definition ghomotopy_group [constructor] (n : ℕ) [is_succ n] (A : Type*) : Group :=
  gtrunc (Ωg[n] A)

  definition aghomotopy_group [constructor] (n : ℕ) [is_at_least_two n] (A : Type*) : AbGroup :=
  agtrunc (Ωag[n] A)

  notation `πg[`:95  n:0 `]`:0 := ghomotopy_group n
  notation `πag[`:95 n:0 `]`:0 := aghomotopy_group n

  definition fundamental_group [constructor] (A : Type*) : Group := πg[1] A

  notation `π₁` := fundamental_group

  definition tr_mul_tr {n : ℕ} {A : Type*} (p q : Ω[n + 1] A) :
    tr p *[πg[n+1] A] tr q = tr (p ⬝ q) :=
  by reflexivity

  definition tr_mul_tr' {n : ℕ} {A : Type*} (p q : Ω[succ n] A)
    : tr p *[π[succ n] A] tr q = tr (p ⬝ q) :=
  idp

  definition homotopy_group_pequiv [constructor] (n : ℕ) {A B : Type*} (H : A ≃* B)
    : π[n] A ≃* π[n] B :=
  ptrunc_pequiv_ptrunc 0 (loopn_pequiv_loopn n H)

  definition homotopy_group_pequiv_loop_ptrunc [constructor] (k : ℕ) (A : Type*) :
    π[k] A ≃* Ω[k] (ptrunc k A) :=
  begin
    refine !loopn_ptrunc_pequiv⁻¹ᵉ* ⬝e* _,
    exact loopn_pequiv_loopn k (pequiv_of_eq begin rewrite [trunc_index.zero_add] end)
  end

  open trunc_index
  definition homotopy_group_ptrunc_of_le [constructor] {k n : ℕ} (H : k ≤ n) (A : Type*) :
    π[k] (ptrunc n A) ≃* π[k] A :=
  calc
    π[k] (ptrunc n A) ≃* Ω[k] (ptrunc k (ptrunc n A))
             : homotopy_group_pequiv_loop_ptrunc k (ptrunc n A)
      ... ≃* Ω[k] (ptrunc k A)
             : loopn_pequiv_loopn k (ptrunc_ptrunc_pequiv_left A (of_nat_le_of_nat H))
      ... ≃* π[k] A : (homotopy_group_pequiv_loop_ptrunc k A)⁻¹ᵉ*

  definition homotopy_group_ptrunc [constructor] (k : ℕ) (A : Type*) :
    π[k] (ptrunc k A) ≃* π[k] A :=
  homotopy_group_ptrunc_of_le (le.refl k) A

  theorem trivial_homotopy_of_is_set (n : ℕ) (A : Type*) [H : is_set A] : πg[n+1] A ≃g G0 :=
  begin
    apply trivial_group_of_is_contr,
    apply is_trunc_trunc_of_is_trunc,
    apply is_contr_loop_of_is_trunc (n+1),
    exact is_trunc_succ_succ_of_is_set _ _ _
  end

  definition homotopy_group_succ_out (n : ℕ) (A : Type*) : π[n + 1] A = π₁ (Ω[n] A) := idp

  definition homotopy_group_succ_in (n : ℕ) (A : Type*) : π[n + 1] A ≃* π[n] (Ω A) :=
  ptrunc_pequiv_ptrunc 0 (loopn_succ_in n A)

  definition ghomotopy_group_succ_out (n : ℕ) (A : Type*) : πg[n + 1] A = π₁ (Ω[n] A) := idp

  definition homotopy_group_succ_in_con {n : ℕ} {A : Type*} (g h : πg[n + 2] A) :
    homotopy_group_succ_in (succ n) A (g * h) =
    homotopy_group_succ_in (succ n) A g * homotopy_group_succ_in (succ n) A h :=
  begin
    induction g with p, induction h with q, esimp,
    apply ap tr, apply loopn_succ_in_con
  end

  definition ghomotopy_group_succ_in [constructor] (n : ℕ) (A : Type*) :
    πg[n + 2] A ≃g πg[n + 1] (Ω A) :=
  begin
    fapply isomorphism_of_equiv,
    { exact homotopy_group_succ_in (succ n) A },
    { exact homotopy_group_succ_in_con },
  end

  definition is_contr_homotopy_group_of_is_contr (n : ℕ) (A : Type*) [is_contr A] : is_contr (π[n] A) :=
  begin
    apply is_trunc_trunc_of_is_trunc,
    apply is_contr_loop_of_is_trunc,
    exact is_trunc_of_is_contr _ _ _
  end

  definition homotopy_group_functor [constructor] (n : ℕ) {A B : Type*} (f : A →* B)
    : π[n] A →* π[n] B :=
  ptrunc_functor 0 (apn n f)

  notation `π→[`:95  n:0 `]`:0 := homotopy_group_functor n

  definition homotopy_group_functor_phomotopy [constructor] (n : ℕ) {A B : Type*} {f g : A →* B}
    (p : f ~* g) : π→[n] f ~* π→[n] g :=
  ptrunc_functor_phomotopy 0 (apn_phomotopy n p)

  definition homotopy_group_functor_pid (n : ℕ) (A : Type*) : π→[n] (pid A) ~* pid (π[n] A) :=
  ptrunc_functor_phomotopy 0 !apn_pid ⬝* !ptrunc_functor_pid

  definition homotopy_group_functor_pcompose [constructor] (n : ℕ) {A B C : Type*} (g : B →* C)
    (f : A →* B) : π→[n] (g ∘* f) ~* π→[n] g ∘* π→[n] f :=
  ptrunc_functor_phomotopy 0 !apn_pcompose ⬝* !ptrunc_functor_pcompose

  definition is_equiv_homotopy_group_functor [constructor] (n : ℕ) {A B : Type*} (f : A →* B)
    (H : is_equiv f) : is_equiv (π→[n] f) :=
  @(is_equiv_trunc_functor 0 _) (is_equiv_apn n f H)

  definition homotopy_group_succ_in_natural (n : ℕ) {A B : Type*} (f : A →* B) :
    psquare (homotopy_group_succ_in n A) (homotopy_group_succ_in n B)
            (π→[n + 1] f) (π→[n] (Ω→ f)) :=
  begin
    exact ptrunc_functor_psquare 0 (loopn_succ_in_natural n f),
  end

  definition homotopy_group_succ_in_natural_unpointed (n : ℕ) {A B : Type*} (f : A →* B) :
    hsquare (homotopy_group_succ_in n A) (homotopy_group_succ_in n B) (π→[n+1] f) (π→[n] (Ω→ f)) :=
  homotopy_group_succ_in_natural n f

  definition is_equiv_homotopy_group_functor_ap1 (n : ℕ) {A B : Type*} (f : A →* B)
    [is_equiv (π→[n + 1] f)] : is_equiv (π→[n] (Ω→ f)) :=
  have is_equiv (π→[n] (Ω→ f) ∘ homotopy_group_succ_in n A),
  from is_equiv_of_equiv_of_homotopy (equiv.mk (π→[n+1] f) _ ⬝e homotopy_group_succ_in n B)
                                     (homotopy_group_succ_in_natural n f)⁻¹*,
  is_equiv.cancel_right (homotopy_group_succ_in n A) _

  definition tinverse [constructor] {X : Type*} : π[1] X →* π[1] X :=
  ptrunc_functor 0 (pinverse X)

  definition is_equiv_tinverse [constructor] (A : Type*) : is_equiv (@tinverse A) :=
  by apply @is_equiv_trunc_functor; apply is_equiv_eq_inverse

  definition ptrunc_functor_pinverse [constructor] {X : Type*}
    : ptrunc_functor 0 (@pinverse X) ~* @tinverse X :=
  begin
    fapply phomotopy.mk,
    { reflexivity},
    { reflexivity}
  end

  /- maybe rename: ghomotopy_group_functor -/
  definition homotopy_group_homomorphism [constructor] (n : ℕ) [H : is_succ n] {A B : Type*}
    (f : A →* B) : πg[n] A →g πg[n] B :=
  gtrunc_functor (Ωg→[n] f)

  definition homotopy_group_functor_mul [constructor] (n : ℕ) {A B : Type*} (g : A →* B)
    (p q : πg[n+1] A) :
    (π→[n + 1] g) (p *[πg[n+1] A] q) = (π→[n+1] g) p *[πg[n+1] B] (π→[n + 1] g) q :=
  begin
    unfold [ghomotopy_group, homotopy_group] at *,
    refine @trunc.rec _ _ _ (λq, !is_trunc_eq) _ p, clear p, intro p,
    refine @trunc.rec _ _ _ (λq, !is_trunc_eq) _ q, clear q, intro q,
    apply ap tr, apply apn_con
  end

  /- todo: rename πg→ -/
  notation `π→g[`:95 n:0 `]`:0 := homotopy_group_homomorphism n

  definition homotopy_group_homomorphism_pcompose (n : ℕ) [H : is_succ n] {A B C : Type*} (g : B →* C)
    (f : A →* B) : π→g[n] (g ∘* f) ~ π→g[n] g ∘ π→g[n] f :=
  begin
    induction H with n, exact to_homotopy (homotopy_group_functor_pcompose (succ n) g f)
  end

  /- todo: use is_succ -/
  definition homotopy_group_isomorphism_of_pequiv [constructor] (n : ℕ) {A B : Type*} (f : A ≃* B)
    : πg[n+1] A ≃g πg[n+1] B :=
  gtrunc_isomorphism_gtrunc (gloopn_isomorphism (n+1) f)

  definition homotopy_group_add (A : Type*) (n m : ℕ) :
    πg[n+m+1] A ≃g πg[n+1] (Ω[m] A) :=
  begin
    revert A, induction m with m IH: intro A,
    { reflexivity},
    { esimp [loopn, nat.add], refine !ghomotopy_group_succ_in ⬝g _, refine !IH ⬝g _,
      apply homotopy_group_isomorphism_of_pequiv,
      exact !loopn_succ_in⁻¹ᵉ*}
  end

  theorem trivial_homotopy_add_of_is_set_loopn {n : ℕ} (m : ℕ) {A : Type*}
    (H : is_set (Ω[n] A)) : πg[m+n+1] A ≃g G0 :=
  !homotopy_group_add ⬝g !trivial_homotopy_of_is_set

  theorem trivial_homotopy_le_of_is_set_loopn {n : ℕ} (m : ℕ) (H1 : n ≤ m) {A : Type*}
    (H2 : is_set (Ω[n] A)) : πg[m+1] A ≃g G0 :=
  obtain (k : ℕ) (p : n + k = m), from le.elim H1,
  isomorphism_of_eq (ap (λx, πg[x+1] A) (p⁻¹ ⬝ add.comm n k)) ⬝g
  trivial_homotopy_add_of_is_set_loopn k H2

  definition homotopy_group_pequiv_loop_ptrunc_con {k : ℕ} {A : Type*} (p q : πg[k +1] A) :
    homotopy_group_pequiv_loop_ptrunc (succ k) A (p * q) =
    homotopy_group_pequiv_loop_ptrunc (succ k) A p ⬝
    homotopy_group_pequiv_loop_ptrunc (succ k) A q :=
  begin
    refine _ ⬝ !loopn_pequiv_loopn_con,
    exact ap (loopn_pequiv_loopn _ _) !loopn_ptrunc_pequiv_inv_con
  end

  definition homotopy_group_pequiv_loop_ptrunc_inv_con {k : ℕ} {A : Type*}
    (p q : Ω[succ k] (ptrunc (succ k) A)) :
    (homotopy_group_pequiv_loop_ptrunc (succ k) A)⁻¹ᵉ* (p ⬝ q) =
    (homotopy_group_pequiv_loop_ptrunc (succ k) A)⁻¹ᵉ* p *
    (homotopy_group_pequiv_loop_ptrunc (succ k) A)⁻¹ᵉ* q :=
  inv_preserve_binary (homotopy_group_pequiv_loop_ptrunc (succ k) A) mul concat
    (@homotopy_group_pequiv_loop_ptrunc_con k A) p q

  definition ghomotopy_group_ptrunc_of_le [constructor] {k n : ℕ} (H : k ≤ n) [Hk : is_succ k] (A : Type*) :
    πg[k] (ptrunc n A) ≃g πg[k] A :=
  begin
    fapply isomorphism_of_equiv,
    { exact homotopy_group_ptrunc_of_le H A},
    { intro g₁ g₂, induction Hk with k,
      refine _ ⬝ !homotopy_group_pequiv_loop_ptrunc_inv_con,
      apply ap ((homotopy_group_pequiv_loop_ptrunc (k+1) A)⁻¹ᵉ*),
      refine _ ⬝ !loopn_pequiv_loopn_con ,
      apply ap (loopn_pequiv_loopn (k+1) _),
      apply homotopy_group_pequiv_loop_ptrunc_con}
  end

  lemma ghomotopy_group_isomorphism_of_ptrunc_pequiv {A B : Type*}
    (n k : ℕ) (H : n+1 ≤[ℕ] k) (f : ptrunc k A ≃* ptrunc k B) : πg[n+1] A ≃g πg[n+1] B :=
  (ghomotopy_group_ptrunc_of_le H A)⁻¹ᵍ ⬝g
  homotopy_group_isomorphism_of_pequiv n f ⬝g
  ghomotopy_group_ptrunc_of_le H B

  definition fundamental_group_isomorphism {X : Type*} {G : Group}
    (e : Ω X ≃ G) (hom_e : Πp q, e (p ⬝ q) = e p * e q) : π₁ X ≃g G :=
  isomorphism_of_equiv (trunc_equiv_trunc 0 e ⬝e (trunc_equiv 0 G))
    begin intro p q, induction p with p, induction q with q, exact hom_e p q end

  definition ghomotopy_group_ptrunc [constructor] (k : ℕ) [is_succ k] (A : Type*) :
    πg[k] (ptrunc k A) ≃g πg[k] A :=
  ghomotopy_group_ptrunc_of_le (le.refl k) A

  section psquare
  variables {A₀₀ A₂₀ A₀₂ A₂₂ : Type*}
            {f₁₀ : A₀₀ →* A₂₀} {f₁₂ : A₀₂ →* A₂₂}
            {f₀₁ : A₀₀ →* A₀₂} {f₂₁ : A₂₀ →* A₂₂}

  definition homotopy_group_functor_psquare (n : ℕ) (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) :
        psquare (π→[n] f₁₀) (π→[n] f₁₂) (π→[n] f₀₁) (π→[n] f₂₁) :=
  !homotopy_group_functor_pcompose⁻¹* ⬝* homotopy_group_functor_phomotopy n p ⬝*
  !homotopy_group_functor_pcompose

  definition homotopy_group_homomorphism_psquare (n : ℕ) [H : is_succ n]
    (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) : hsquare (π→g[n] f₁₀) (π→g[n] f₁₂) (π→g[n] f₀₁) (π→g[n] f₂₁) :=
  begin
    induction H with n, exact to_homotopy (ptrunc_functor_psquare 0 (apn_psquare (succ n) p))
  end

  end psquare

  /- some homomorphisms -/

  -- definition is_homomorphism_cast_loopn_succ_eq_in (n : ℕ) {A : Type*} :
  --   is_homomorphism (loopn_succ_in A (succ n) : πg[n+1+1] A → πg[n+1] (Ω A)) :=
  -- begin
  --   intro g h, induction g with g, induction h with h,
  --   xrewrite [tr_mul_tr, - + fn_cast_eq_cast_fn _ (λn, tr), tr_mul_tr, ↑cast, -tr_compose,
  --             loopn_succ_eq_in_concat, - + tr_compose],
  -- end

  definition is_mul_hom_inverse (n : ℕ) (A : Type*)
    : is_mul_hom (λp, p⁻¹ : (πag[n+2] A) → (πag[n+2] A)) :=
  begin
    intro g h, exact ap inv (mul.comm g h) ⬝ mul_inv h g,
  end

end eq
