/-
Copyright (c) 2017 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

More results about pointed types.

Contains
- squares of pointed maps,
- equalities between pointed homotopies and
- squares between pointed homotopies
- pointed maps into and out of (ppmap A B), the pointed type of pointed maps from A to B
-/


import algebra.homotopy_group eq2

open pointed eq unit is_trunc trunc nat group is_equiv equiv sigma function bool

namespace pointed
  variables {A B C : Type*}

  section psquare
  /-
    Squares of pointed maps

    We treat expressions of the form
      psquare f g h k :≡ k ∘* f ~* g ∘* h
    as squares, where f is the top, g is the bottom, h is the left face and k is the right face.
    Then the following are operations on squares
  -/

  variables {A' A₀₀ A₂₀ A₄₀ A₀₂ A₂₂ A₄₂ A₀₄ A₂₄ A₄₄ : Type*}
            {f₁₀ f₁₀' : A₀₀ →* A₂₀} {f₃₀ : A₂₀ →* A₄₀}
            {f₀₁ f₀₁' : A₀₀ →* A₀₂} {f₂₁ f₂₁' : A₂₀ →* A₂₂} {f₄₁ : A₄₀ →* A₄₂}
            {f₁₂ f₁₂' : A₀₂ →* A₂₂} {f₃₂ : A₂₂ →* A₄₂}
            {f₀₃ : A₀₂ →* A₀₄} {f₂₃ : A₂₂ →* A₂₄} {f₄₃ : A₄₂ →* A₄₄}
            {f₁₄ : A₀₄ →* A₂₄} {f₃₄ : A₂₄ →* A₄₄}

  definition psquare [reducible] (f₁₀ : A₀₀ →* A₂₀) (f₁₂ : A₀₂ →* A₂₂)
                                 (f₀₁ : A₀₀ →* A₀₂) (f₂₁ : A₂₀ →* A₂₂) : Type :=
  f₂₁ ∘* f₁₀ ~* f₁₂ ∘* f₀₁

  definition psquare_of_phomotopy (p : f₂₁ ∘* f₁₀ ~* f₁₂ ∘* f₀₁) : psquare f₁₀ f₁₂ f₀₁ f₂₁ :=
  p

  definition phomotopy_of_psquare (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) : f₂₁ ∘* f₁₀ ~* f₁₂ ∘* f₀₁ :=
  p

  definition phdeg_square {f f' : A →* A'} (p : f ~* f') : psquare !pid !pid f f' :=
  !pcompose_pid ⬝* p⁻¹* ⬝* !pid_pcompose⁻¹*
  definition pvdeg_square {f f' : A →* A'} (p : f ~* f') : psquare f f' !pid !pid :=
  !pid_pcompose ⬝* p ⬝* !pcompose_pid⁻¹*

  variables (f₀₁ f₁₀)
  definition phrefl : psquare !pid !pid f₀₁ f₀₁ := phdeg_square phomotopy.rfl
  definition pvrefl : psquare f₁₀ f₁₀ !pid !pid := pvdeg_square phomotopy.rfl
  variables {f₀₁ f₁₀}
  definition phrfl : psquare !pid !pid f₀₁ f₀₁ := phrefl f₀₁
  definition pvrfl : psquare f₁₀ f₁₀ !pid !pid := pvrefl f₁₀

  definition phconcat (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) (q : psquare f₃₀ f₃₂ f₂₁ f₄₁) :
    psquare (f₃₀ ∘* f₁₀) (f₃₂ ∘* f₁₂) f₀₁ f₄₁ :=
  !passoc⁻¹* ⬝* pwhisker_right f₁₀ q ⬝* !passoc ⬝* pwhisker_left f₃₂ p ⬝* !passoc⁻¹*

  definition pvconcat (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) (q : psquare f₁₂ f₁₄ f₀₃ f₂₃) :
    psquare f₁₀ f₁₄ (f₀₃ ∘* f₀₁) (f₂₃ ∘* f₂₁) :=
  !passoc ⬝* pwhisker_left _ p ⬝* !passoc⁻¹* ⬝* pwhisker_right _ q ⬝* !passoc

  definition phinverse {f₁₀ : A₀₀ ≃* A₂₀} {f₁₂ : A₀₂ ≃* A₂₂} (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) :
    psquare f₁₀⁻¹ᵉ* f₁₂⁻¹ᵉ* f₂₁ f₀₁ :=
  !pid_pcompose⁻¹* ⬝* pwhisker_right _ (pleft_inv f₁₂)⁻¹* ⬝* !passoc ⬝*
  pwhisker_left _
    (!passoc⁻¹* ⬝* pwhisker_right _ p⁻¹* ⬝* !passoc ⬝* pwhisker_left _ !pright_inv ⬝* !pcompose_pid)

  definition pvinverse {f₀₁ : A₀₀ ≃* A₀₂} {f₂₁ : A₂₀ ≃* A₂₂} (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) :
    psquare f₁₂ f₁₀ f₀₁⁻¹ᵉ* f₂₁⁻¹ᵉ* :=
  (phinverse p⁻¹*)⁻¹*

  definition phomotopy_hconcat (q : f₀₁' ~* f₀₁) (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) :
    psquare f₁₀ f₁₂ f₀₁' f₂₁ :=
  p ⬝* pwhisker_left f₁₂ q⁻¹*

  definition hconcat_phomotopy (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) (q : f₂₁' ~* f₂₁) :
    psquare f₁₀ f₁₂ f₀₁ f₂₁' :=
  pwhisker_right f₁₀ q ⬝* p

  definition phomotopy_vconcat (q : f₁₀' ~* f₁₀) (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) :
    psquare f₁₀' f₁₂ f₀₁ f₂₁ :=
  pwhisker_left f₂₁ q ⬝* p

  definition vconcat_phomotopy (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) (q : f₁₂' ~* f₁₂) :
    psquare f₁₀ f₁₂' f₀₁ f₂₁ :=
  p ⬝* pwhisker_right f₀₁ q⁻¹*

  infix ` ⬝h* `:73 := phconcat
  infix ` ⬝v* `:73 := pvconcat
  infixl ` ⬝hp* `:72 := hconcat_phomotopy
  infixr ` ⬝ph* `:72 := phomotopy_hconcat
  infixl ` ⬝vp* `:72 := vconcat_phomotopy
  infixr ` ⬝pv* `:72 := phomotopy_vconcat
  postfix `⁻¹ʰ*`:(max+1) := phinverse
  postfix `⁻¹ᵛ*`:(max+1) := pvinverse

  definition pwhisker_tl (f : A →* A₀₀) (q : psquare f₁₀ f₁₂ f₀₁ f₂₁) :
    psquare (f₁₀ ∘* f) f₁₂ (f₀₁ ∘* f) f₂₁ :=
  !passoc⁻¹* ⬝* pwhisker_right f q ⬝* !passoc

  definition ap1_psquare (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) :
    psquare (Ω→ f₁₀) (Ω→ f₁₂) (Ω→ f₀₁) (Ω→ f₂₁) :=
  !ap1_pcompose⁻¹* ⬝* ap1_phomotopy p ⬝* !ap1_pcompose

  definition apn_psquare (n : ℕ) (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) :
    psquare (Ω→[n] f₁₀) (Ω→[n] f₁₂) (Ω→[n] f₀₁) (Ω→[n] f₂₁) :=
  !apn_pcompose⁻¹* ⬝* apn_phomotopy n p ⬝* !apn_pcompose

  definition ptrunc_functor_psquare (n : ℕ₋₂) (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) :
    psquare (ptrunc_functor n f₁₀) (ptrunc_functor n f₁₂)
            (ptrunc_functor n f₀₁) (ptrunc_functor n f₂₁) :=
  !ptrunc_functor_pcompose⁻¹* ⬝* ptrunc_functor_phomotopy n p ⬝* !ptrunc_functor_pcompose

  definition homotopy_group_functor_psquare (n : ℕ) (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) :
        psquare (π→[n] f₁₀) (π→[n] f₁₂) (π→[n] f₀₁) (π→[n] f₂₁) :=
  !homotopy_group_functor_compose⁻¹* ⬝* homotopy_group_functor_phomotopy n p ⬝*
  !homotopy_group_functor_compose

  definition homotopy_group_homomorphism_psquare (n : ℕ) [H : is_succ n]
    (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) : hsquare (π→g[n] f₁₀) (π→g[n] f₁₂) (π→g[n] f₀₁) (π→g[n] f₂₁) :=
  begin
    induction H with n, exact to_homotopy (ptrunc_functor_psquare 0 (apn_psquare (succ n) p))
  end

  end psquare

  definition punit_pmap_phomotopy [constructor] {A : Type*} (f : punit →* A) :
    f ~* pconst punit A :=
  begin
    fapply phomotopy.mk,
    { intro u, induction u, exact respect_pt f },
    { reflexivity }
  end

  definition is_contr_punit_pmap (A : Type*) : is_contr (punit →* A) :=
  is_contr.mk (pconst punit A) (λf, eq_of_phomotopy (punit_pmap_phomotopy f)⁻¹*)

  definition phomotopy_eq_equiv {A B : Type*} {f g : A →* B} (h k : f ~* g) :
    (h = k) ≃ Σ(p : to_homotopy h ~ to_homotopy k),
      whisker_right (respect_pt g) (p pt) ⬝ to_homotopy_pt k = to_homotopy_pt h :=
  calc
    h = k ≃ phomotopy.sigma_char _ _ h = phomotopy.sigma_char _ _ k
      : eq_equiv_fn_eq (phomotopy.sigma_char f g) h k
      ... ≃ Σ(p : to_homotopy h = to_homotopy k),
              pathover (λp, p pt ⬝ respect_pt g = respect_pt f) (to_homotopy_pt h) p (to_homotopy_pt k)
      : sigma_eq_equiv _ _
      ... ≃ Σ(p : to_homotopy h = to_homotopy k),
              to_homotopy_pt h = ap (λq, q pt ⬝ respect_pt g) p ⬝ to_homotopy_pt k
      : sigma_equiv_sigma_right (λp, eq_pathover_equiv_Fl p (to_homotopy_pt h) (to_homotopy_pt k))
      ... ≃ Σ(p : to_homotopy h = to_homotopy k),
              ap (λq, q pt ⬝ respect_pt g) p ⬝ to_homotopy_pt k = to_homotopy_pt h
      : sigma_equiv_sigma_right (λp, eq_equiv_eq_symm _ _)
      ... ≃ Σ(p : to_homotopy h = to_homotopy k),
      whisker_right (respect_pt g) (apd10 p pt) ⬝ to_homotopy_pt k = to_homotopy_pt h
      : sigma_equiv_sigma_right (λp, equiv_eq_closed_left _ (whisker_right _ !whisker_right_ap⁻¹))
      ... ≃ Σ(p : to_homotopy h ~ to_homotopy k),
      whisker_right (respect_pt g) (p pt) ⬝ to_homotopy_pt k = to_homotopy_pt h
      : sigma_equiv_sigma_left' eq_equiv_homotopy

  definition phomotopy_eq {A B : Type*} {f g : A →* B} {h k : f ~* g} (p : to_homotopy h ~ to_homotopy k)
    (q : whisker_right (respect_pt g) (p pt) ⬝ to_homotopy_pt k = to_homotopy_pt h) : h = k :=
  to_inv (phomotopy_eq_equiv h k) ⟨p, q⟩

  definition phomotopy_eq' {A B : Type*} {f g : A →* B} {h k : f ~* g} (p : to_homotopy h ~ to_homotopy k)
    (q : square (to_homotopy_pt h) (to_homotopy_pt k) (whisker_right (respect_pt g) (p pt)) idp) : h = k :=
  phomotopy_eq p (eq_of_square q)⁻¹

  definition trans_refl {A B : Type*} {f g : A →* B} (p : f ~* g) : p ⬝* phomotopy.refl g = p :=
  begin
    induction A with A a₀, induction B with B b₀,
    induction f with f f₀, induction g with g g₀, induction p with p p₀,
    esimp at *, induction g₀, induction p₀,
    reflexivity
  end

  definition eq_of_phomotopy_trans {X Y : Type*} {f g h : X →* Y} (p : f ~* g) (q : g ~* h) :
    eq_of_phomotopy (p ⬝* q) = eq_of_phomotopy p ⬝ eq_of_phomotopy q :=
  begin
    induction p using phomotopy_rec_idp, induction q using phomotopy_rec_idp,
    exact ap eq_of_phomotopy !trans_refl ⬝ whisker_left _ !eq_of_phomotopy_refl⁻¹
  end

  definition refl_trans {A B : Type*} {f g : A →* B} (p : f ~* g) : phomotopy.refl f ⬝* p = p :=
  begin
    induction p using phomotopy_rec_idp,
    induction A with A a₀, induction B with B b₀,
    induction f with f f₀, esimp at *, induction f₀,
    reflexivity
  end

  definition trans_assoc {A B : Type*} {f g h i : A →* B} (p : f ~* g) (q : g ~* h)
    (r : h ~* i) : p ⬝* q ⬝* r = p ⬝* (q ⬝* r) :=
  begin
    induction r using phomotopy_rec_idp,
    induction q using phomotopy_rec_idp,
    induction p using phomotopy_rec_idp,
    induction B with B b₀,
    induction f with f f₀, esimp at *, induction f₀,
    reflexivity
  end

  definition refl_symm {A B : Type*} (f : A →* B) : phomotopy.rfl⁻¹* = phomotopy.refl f :=
  begin
    induction B with B b₀,
    induction f with f f₀, esimp at *, induction f₀,
    reflexivity
  end

  definition symm_symm {A B : Type*} {f g : A →* B} (p : f ~* g) : p⁻¹*⁻¹* = p :=
  phomotopy_eq (λa, !inv_inv)
    begin
      induction p using phomotopy_rec_idp, induction f with f f₀, induction B with B b₀,
      esimp at *, induction f₀, reflexivity
    end

  definition trans_right_inv {A B : Type*} {f g : A →* B} (p : f ~* g) : p ⬝* p⁻¹* = phomotopy.rfl :=
  begin
    induction p using phomotopy_rec_idp, exact !refl_trans ⬝ !refl_symm
  end

  definition trans_left_inv {A B : Type*} {f g : A →* B} (p : f ~* g) : p⁻¹* ⬝* p = phomotopy.rfl :=
  begin
    induction p using phomotopy_rec_idp, exact !trans_refl ⬝ !refl_symm
  end

  definition trans2 {A B : Type*} {f g h : A →* B} {p p' : f ~* g} {q q' : g ~* h}
    (r : p = p') (s : q = q') : p ⬝* q = p' ⬝* q' :=
  ap011 phomotopy.trans r s

  definition pcompose3 {A B C : Type*} {g g' : B →* C} {f f' : A →* B}
  {p p' : g ~* g'} {q q' : f ~* f'} (r : p = p') (s : q = q') : p ◾* q = p' ◾* q' :=
  ap011 pcompose2 r s

  definition symm2 {A B : Type*} {f g : A →* B} {p p' : f ~* g} (r : p = p') : p⁻¹* = p'⁻¹* :=
  ap phomotopy.symm r

  infixl ` ◾** `:80 := pointed.trans2
  infixl ` ◽* `:81 := pointed.pcompose3
  postfix `⁻²**`:(max+1) := pointed.symm2

  definition trans_symm {A B : Type*} {f g h : A →* B} (p : f ~* g) (q : g ~* h) :
    (p ⬝* q)⁻¹* = q⁻¹* ⬝* p⁻¹* :=
  begin
    induction p using phomotopy_rec_idp, induction q using phomotopy_rec_idp,
    exact !trans_refl⁻²** ⬝ !trans_refl⁻¹ ⬝ idp ◾** !refl_symm⁻¹
  end

  definition phwhisker_left {A B : Type*} {f g h : A →* B} (p : f ~* g) {q q' : g ~* h}
    (s : q = q') : p ⬝* q = p ⬝* q' :=
  idp ◾** s

  definition phwhisker_right {A B : Type*} {f g h : A →* B} {p p' : f ~* g} (q : g ~* h)
    (r : p = p') : p ⬝* q = p' ⬝* q :=
  r ◾** idp

  definition pwhisker_left_refl {A B C : Type*} (g : B →* C) (f : A →* B) :
    pwhisker_left g (phomotopy.refl f) = phomotopy.refl (g ∘* f) :=
  begin
    induction A with A a₀, induction B with B b₀, induction C with C c₀,
    induction f with f f₀, induction g with g g₀,
    esimp at *, induction g₀, induction f₀, reflexivity
  end

  definition pwhisker_right_refl {A B C : Type*} (f : A →* B) (g : B →* C) :
    pwhisker_right f (phomotopy.refl g) = phomotopy.refl (g ∘* f) :=
  begin
    induction A with A a₀, induction B with B b₀, induction C with C c₀,
    induction f with f f₀, induction g with g g₀,
    esimp at *, induction g₀, induction f₀, reflexivity
  end

  definition pcompose2_refl {A B C : Type*} (g : B →* C) (f : A →* B) :
    phomotopy.refl g ◾* phomotopy.refl f = phomotopy.rfl :=
  !pwhisker_right_refl ◾** !pwhisker_left_refl ⬝ !refl_trans

  definition pcompose2_refl_left {A B C : Type*} (g : B →* C) {f f' : A →* B} (p : f ~* f') :
    phomotopy.rfl ◾* p = pwhisker_left g p :=
  !pwhisker_right_refl ◾** idp ⬝ !refl_trans

  definition pcompose2_refl_right {A B C : Type*} {g g' : B →* C} (f : A →* B) (p : g ~* g') :
    p ◾* phomotopy.rfl = pwhisker_right f p :=
  idp ◾** !pwhisker_left_refl ⬝ !trans_refl

  definition pwhisker_left_trans {A B C : Type*} (g : B →* C) {f₁ f₂ f₃ : A →* B}
    (p : f₁ ~* f₂) (q : f₂ ~* f₃) :
    pwhisker_left g (p ⬝* q) = pwhisker_left g p ⬝* pwhisker_left g q :=
  begin
    induction p using phomotopy_rec_idp,
    induction q using phomotopy_rec_idp,
    refine _ ⬝ !pwhisker_left_refl⁻¹ ◾** !pwhisker_left_refl⁻¹,
    refine ap (pwhisker_left g) !trans_refl ⬝ !pwhisker_left_refl ⬝ !trans_refl⁻¹
  end

  definition pwhisker_right_trans {A B C : Type*} (f : A →* B) {g₁ g₂ g₃ : B →* C}
    (p : g₁ ~* g₂) (q : g₂ ~* g₃) :
    pwhisker_right f (p ⬝* q) = pwhisker_right f p ⬝* pwhisker_right f q :=
  begin
    induction p using phomotopy_rec_idp,
    induction q using phomotopy_rec_idp,
    refine _ ⬝ !pwhisker_right_refl⁻¹ ◾** !pwhisker_right_refl⁻¹,
    refine ap (pwhisker_right f) !trans_refl ⬝ !pwhisker_right_refl ⬝ !trans_refl⁻¹
  end

  definition pwhisker_left_symm {A B C : Type*} (g : B →* C) {f₁ f₂ : A →* B} (p : f₁ ~* f₂) :
    pwhisker_left g p⁻¹* = (pwhisker_left g p)⁻¹* :=
  begin
    induction p using phomotopy_rec_idp,
    refine _ ⬝ ap phomotopy.symm !pwhisker_left_refl⁻¹,
    refine ap (pwhisker_left g) !refl_symm ⬝ !pwhisker_left_refl ⬝ !refl_symm⁻¹
  end

  definition pwhisker_right_symm {A B C : Type*} (f : A →* B) {g₁ g₂ : B →* C} (p : g₁ ~* g₂) :
    pwhisker_right f p⁻¹* = (pwhisker_right f p)⁻¹* :=
  begin
    induction p using phomotopy_rec_idp,
    refine _ ⬝ ap phomotopy.symm !pwhisker_right_refl⁻¹,
    refine ap (pwhisker_right f) !refl_symm ⬝ !pwhisker_right_refl ⬝ !refl_symm⁻¹
  end

  definition trans_eq_of_eq_symm_trans {A B : Type*} {f g h : A →* B} {p : f ~* g} {q : g ~* h}
    {r : f ~* h} (s : q = p⁻¹* ⬝* r) : p ⬝* q = r :=
  idp ◾** s ⬝ !trans_assoc⁻¹ ⬝ trans_right_inv p ◾** idp ⬝ !refl_trans

  definition eq_symm_trans_of_trans_eq {A B : Type*} {f g h : A →* B} {p : f ~* g} {q : g ~* h}
    {r : f ~* h} (s : p ⬝* q = r) : q = p⁻¹* ⬝* r :=
  !refl_trans⁻¹ ⬝ !trans_left_inv⁻¹ ◾** idp ⬝ !trans_assoc ⬝ idp ◾** s

  definition trans_eq_of_eq_trans_symm {A B : Type*} {f g h : A →* B} {p : f ~* g} {q : g ~* h}
    {r : f ~* h} (s : p = r ⬝* q⁻¹*) : p ⬝* q = r :=
  s ◾** idp ⬝ !trans_assoc ⬝ idp ◾** trans_left_inv q ⬝ !trans_refl

  definition eq_trans_symm_of_trans_eq {A B : Type*} {f g h : A →* B} {p : f ~* g} {q : g ~* h}
    {r : f ~* h} (s : p ⬝* q = r) : p = r ⬝* q⁻¹* :=
  !trans_refl⁻¹ ⬝ idp ◾** !trans_right_inv⁻¹ ⬝ !trans_assoc⁻¹ ⬝ s ◾** idp

  definition eq_trans_of_symm_trans_eq {A B : Type*} {f g h : A →* B} {p : f ~* g} {q : g ~* h}
    {r : f ~* h} (s : p⁻¹* ⬝* r = q) : r = p ⬝* q :=
  !refl_trans⁻¹ ⬝ !trans_right_inv⁻¹ ◾** idp ⬝ !trans_assoc ⬝ idp ◾** s

  definition symm_trans_eq_of_eq_trans {A B : Type*} {f g h : A →* B} {p : f ~* g} {q : g ~* h}
    {r : f ~* h} (s : r = p ⬝* q) : p⁻¹* ⬝* r = q :=
  idp ◾** s ⬝ !trans_assoc⁻¹ ⬝ trans_left_inv p ◾** idp ⬝ !refl_trans

  definition eq_trans_of_trans_symm_eq {A B : Type*} {f g h : A →* B} {p : f ~* g} {q : g ~* h}
    {r : f ~* h} (s : r ⬝* q⁻¹* = p) : r = p ⬝* q :=
  !trans_refl⁻¹ ⬝ idp ◾** !trans_left_inv⁻¹ ⬝ !trans_assoc⁻¹ ⬝ s ◾** idp

  definition trans_symm_eq_of_eq_trans {A B : Type*} {f g h : A →* B} {p : f ~* g} {q : g ~* h}
    {r : f ~* h} (s : r = p ⬝* q) : r ⬝* q⁻¹* = p :=
  s ◾** idp ⬝ !trans_assoc ⬝ idp ◾** trans_right_inv q ⬝ !trans_refl

  section phsquare
  /-
    Squares of pointed homotopies
  -/

  variables {f f' f₀₀ f₂₀ f₄₀ f₀₂ f₂₂ f₄₂ f₀₄ f₂₄ f₄₄ : A →* B}
            {p₁₀ : f₀₀ ~* f₂₀} {p₃₀ : f₂₀ ~* f₄₀}
            {p₀₁ : f₀₀ ~* f₀₂} {p₂₁ : f₂₀ ~* f₂₂} {p₄₁ : f₄₀ ~* f₄₂}
            {p₁₂ : f₀₂ ~* f₂₂} {p₃₂ : f₂₂ ~* f₄₂}
            {p₀₃ : f₀₂ ~* f₀₄} {p₂₃ : f₂₂ ~* f₂₄} {p₄₃ : f₄₂ ~* f₄₄}
            {p₁₄ : f₀₄ ~* f₂₄} {p₃₄ : f₂₄ ~* f₄₄}

  definition phsquare [reducible] (p₁₀ : f₀₀ ~* f₂₀) (p₁₂ : f₀₂ ~* f₂₂)
                                  (p₀₁ : f₀₀ ~* f₀₂) (p₂₁ : f₂₀ ~* f₂₂) : Type :=
  p₁₀ ⬝* p₂₁ = p₀₁ ⬝* p₁₂

  definition phsquare_of_eq (p : p₁₀ ⬝* p₂₁ = p₀₁ ⬝* p₁₂) : phsquare p₁₀ p₁₂ p₀₁ p₂₁ := p
  definition eq_of_phsquare (p : phsquare p₁₀ p₁₂ p₀₁ p₂₁) : p₁₀ ⬝* p₂₁ = p₀₁ ⬝* p₁₂ := p

  -- definition phsquare.mk (p : Πx, square (p₁₀ x) (p₁₂ x) (p₀₁ x) (p₂₁ x))
  --   (q : cube (square_of_eq (to_homotopy_pt p₁₀)) (square_of_eq (to_homotopy_pt p₁₂))
  --             (square_of_eq (to_homotopy_pt p₀₁)) (square_of_eq (to_homotopy_pt p₂₁))
  --             (p pt) ids) : phsquare p₁₀ p₁₂ p₀₁ p₂₁ :=
  -- begin
  --   fapply phomotopy_eq,
  --   { intro x, apply eq_of_square (p x) },
  --   { generalize p pt, intro r, exact sorry }
  -- end


  definition phhconcat (p : phsquare p₁₀ p₁₂ p₀₁ p₂₁) (q : phsquare p₃₀ p₃₂ p₂₁ p₄₁) :
    phsquare (p₁₀ ⬝* p₃₀) (p₁₂ ⬝* p₃₂) p₀₁ p₄₁ :=
  !trans_assoc ⬝ idp ◾** q ⬝ !trans_assoc⁻¹ ⬝ p ◾** idp ⬝ !trans_assoc

  definition phvconcat (p : phsquare p₁₀ p₁₂ p₀₁ p₂₁) (q : phsquare p₁₂ p₁₄ p₀₃ p₂₃) :
    phsquare p₁₀ p₁₄ (p₀₁ ⬝* p₀₃) (p₂₁ ⬝* p₂₃) :=
  (phhconcat p⁻¹ q⁻¹)⁻¹

  definition phhdeg_square {p₁ p₂ : f ~* f'} (q : p₁ = p₂) : phsquare phomotopy.rfl phomotopy.rfl p₁ p₂ :=
  !refl_trans ⬝ q⁻¹ ⬝ !trans_refl⁻¹
  definition phvdeg_square {p₁ p₂ : f ~* f'} (q : p₁ = p₂) : phsquare p₁ p₂ phomotopy.rfl phomotopy.rfl :=
  !trans_refl ⬝ q ⬝ !refl_trans⁻¹

  variables (p₀₁ p₁₀)
  definition phhrefl : phsquare phomotopy.rfl phomotopy.rfl p₀₁ p₀₁ := phhdeg_square idp
  definition phvrefl : phsquare p₁₀ p₁₀ phomotopy.rfl phomotopy.rfl := phvdeg_square idp
  variables {p₀₁ p₁₀}
  definition phhrfl : phsquare phomotopy.rfl phomotopy.rfl p₀₁ p₀₁ := phhrefl p₀₁
  definition phvrfl : phsquare p₁₀ p₁₀ phomotopy.rfl phomotopy.rfl := phvrefl p₁₀

  /-
    The names are very baroque. The following stands for
    "pointed homotopy path-horizontal composition" (i.e. composition on the left with a path)
    The names are obtained by using the ones for squares, and putting "ph" in front of it.
    In practice, use the notation ⬝ph** defined below, which might be easier to remember
  -/
  definition phphconcat {p₀₁'} (p : p₀₁' = p₀₁) (q : phsquare p₁₀ p₁₂ p₀₁ p₂₁) :
    phsquare p₁₀ p₁₂ p₀₁' p₂₁ :=
  by induction p; exact q

  definition phhpconcat {p₂₁'} (q : phsquare p₁₀ p₁₂ p₀₁ p₂₁) (p : p₂₁ = p₂₁') :
    phsquare p₁₀ p₁₂ p₀₁ p₂₁' :=
  by induction p; exact q

  definition phpvconcat {p₁₀'} (p : p₁₀' = p₁₀) (q : phsquare p₁₀ p₁₂ p₀₁ p₂₁) :
    phsquare p₁₀' p₁₂ p₀₁ p₂₁ :=
  by induction p; exact q

  definition phvpconcat {p₁₂'} (q : phsquare p₁₀ p₁₂ p₀₁ p₂₁) (p : p₁₂ = p₁₂') :
    phsquare p₁₀ p₁₂' p₀₁ p₂₁ :=
  by induction p; exact q

  definition phhinverse (p : phsquare p₁₀ p₁₂ p₀₁ p₂₁) : phsquare p₁₀⁻¹* p₁₂⁻¹* p₂₁ p₀₁ :=
  begin
    refine (eq_symm_trans_of_trans_eq _)⁻¹,
    refine !trans_assoc⁻¹ ⬝ _,
    refine (eq_trans_symm_of_trans_eq _)⁻¹,
    exact (eq_of_phsquare p)⁻¹
  end

  definition phvinverse (p : phsquare p₁₀ p₁₂ p₀₁ p₂₁) : phsquare p₁₂ p₁₀ p₀₁⁻¹* p₂₁⁻¹* :=
  (phhinverse p⁻¹)⁻¹

  infix ` ⬝h** `:78 := phhconcat
  infix ` ⬝v** `:78 := phvconcat
  infixr ` ⬝ph** `:77 := phphconcat
  infixl ` ⬝hp** `:77 := phhpconcat
  infixr ` ⬝pv** `:77 := phpvconcat
  infixl ` ⬝vp** `:77 := phvpconcat
  postfix `⁻¹ʰ**`:(max+1) := phhinverse
  postfix `⁻¹ᵛ**`:(max+1) := phvinverse

  definition phwhisker_rt (p : f ~* f₂₀) (q : phsquare p₁₀ p₁₂ p₀₁ p₂₁) :
    phsquare (p₁₀ ⬝* p⁻¹*) p₁₂ p₀₁ (p ⬝* p₂₁) :=
  !trans_assoc ⬝ idp ◾** (!trans_assoc⁻¹ ⬝ !trans_left_inv ◾** idp ⬝ !refl_trans) ⬝ q

  definition phwhisker_br (p : f₂₂ ~* f) (q : phsquare p₁₀ p₁₂ p₀₁ p₂₁) :
    phsquare p₁₀ (p₁₂ ⬝* p) p₀₁ (p₂₁ ⬝* p) :=
  !trans_assoc⁻¹ ⬝ q ◾** idp ⬝ !trans_assoc

  definition phmove_top_of_left' {p₀₁ : f ~* f₀₂} (p : f₀₀ ~* f)
    (q : phsquare p₁₀ p₁₂ (p ⬝* p₀₁) p₂₁) : phsquare (p⁻¹* ⬝* p₁₀) p₁₂ p₀₁ p₂₁ :=
  !trans_assoc ⬝ (eq_symm_trans_of_trans_eq (q ⬝ !trans_assoc)⁻¹)⁻¹

  definition phmove_bot_of_left {p₀₁ : f₀₀ ~* f} (p : f ~* f₀₂)
    (q : phsquare p₁₀ p₁₂ (p₀₁ ⬝* p) p₂₁) : phsquare p₁₀ (p ⬝* p₁₂) p₀₁ p₂₁ :=
  q ⬝ !trans_assoc

  definition passoc_phomotopy_right {A B C D : Type*} (h : C →* D) (g : B →* C) {f f' : A →* B}
    (p : f ~* f') : phsquare (passoc h g f) (passoc h g f')
      (pwhisker_left (h ∘* g) p) (pwhisker_left h (pwhisker_left g p)) :=
  begin
    induction p using phomotopy_rec_idp,
    refine idp ◾** (ap (pwhisker_left h) !pwhisker_left_refl ⬝ !pwhisker_left_refl) ⬝ _ ⬝
          !pwhisker_left_refl⁻¹ ◾** idp,
    exact !trans_refl ⬝ !refl_trans⁻¹
  end

  theorem passoc_phomotopy_middle {A B C D : Type*} (h : C →* D) {g g' : B →* C} (f : A →* B)
    (p : g ~* g') : phsquare (passoc h g f) (passoc h g' f)
      (pwhisker_right f (pwhisker_left h p)) (pwhisker_left h (pwhisker_right f p)) :=
  begin
    induction p using phomotopy_rec_idp,
    rewrite [pwhisker_right_refl, pwhisker_left_refl],
    rewrite [pwhisker_right_refl, pwhisker_left_refl],
    exact phvrfl
  end

  definition pwhisker_right_pwhisker_left {A B C : Type*} {g g' : B →* C} {f f' : A →* B}
    (p : g ~* g') (q : f ~* f') :
    phsquare (pwhisker_right f p) (pwhisker_right f' p) (pwhisker_left g q) (pwhisker_left g' q) :=
  begin
    induction p using phomotopy_rec_idp,
    induction q using phomotopy_rec_idp,
    exact !pwhisker_right_refl ◾** !pwhisker_left_refl ⬝
          !pwhisker_left_refl⁻¹ ◾** !pwhisker_right_refl⁻¹
  end

  definition pwhisker_left_phsquare (f : B →* C) (p : phsquare p₁₀ p₁₂ p₀₁ p₂₁) :
    phsquare (pwhisker_left f p₁₀) (pwhisker_left f p₁₂)
             (pwhisker_left f p₀₁) (pwhisker_left f p₂₁) :=
  !pwhisker_left_trans⁻¹ ⬝ ap (pwhisker_left f) p ⬝ !pwhisker_left_trans

  definition pwhisker_right_phsquare (f : C →* A) (p : phsquare p₁₀ p₁₂ p₀₁ p₂₁) :
    phsquare (pwhisker_right f p₁₀) (pwhisker_right f p₁₂)
             (pwhisker_right f p₀₁) (pwhisker_right f p₂₁) :=
  !pwhisker_right_trans⁻¹ ⬝ ap (pwhisker_right f) p ⬝ !pwhisker_right_trans

  end phsquare

  definition phomotopy_of_eq_con {A B : Type*} {f g h : A →* B} (p : f = g) (q : g = h) :
    phomotopy_of_eq (p ⬝ q) = phomotopy_of_eq p ⬝* phomotopy_of_eq q :=
  begin induction q, induction p, exact !trans_refl⁻¹ end

  definition pcompose_left_eq_of_phomotopy {A B C : Type*} (g : B →* C) {f f' : A →* B}
    (H : f ~* f') : ap (λf, g ∘* f) (eq_of_phomotopy H) = eq_of_phomotopy (pwhisker_left g H) :=
  begin
    induction H using phomotopy_rec_idp,
    refine ap02 _ !eq_of_phomotopy_refl ⬝ !eq_of_phomotopy_refl⁻¹ ⬝ ap eq_of_phomotopy _,
    exact !pwhisker_left_refl⁻¹
  end

  definition pcompose_right_eq_of_phomotopy {A B C : Type*} {g g' : B →* C} (f : A →* B)
    (H : g ~* g') : ap (λg, g ∘* f) (eq_of_phomotopy H) = eq_of_phomotopy (pwhisker_right f H) :=
  begin
    induction H using phomotopy_rec_idp,
    refine ap02 _ !eq_of_phomotopy_refl ⬝ !eq_of_phomotopy_refl⁻¹ ⬝ ap eq_of_phomotopy _,
    exact !pwhisker_right_refl⁻¹
  end

  definition phomotopy_of_eq_pcompose_left {A B C : Type*} (g : B →* C) {f f' : A →* B}
    (p : f = f') : phomotopy_of_eq (ap (λf, g ∘* f) p) = pwhisker_left g (phomotopy_of_eq p) :=
  begin
    induction p, exact !pwhisker_left_refl⁻¹
  end

  definition phomotopy_of_eq_pcompose_right {A B C : Type*} {g g' : B →* C} (f : A →* B)
    (p : g = g') : phomotopy_of_eq (ap (λg, g ∘* f) p) = pwhisker_right f (phomotopy_of_eq p) :=
  begin
    induction p, exact !pwhisker_right_refl⁻¹
  end

  definition phomotopy_mk_ppmap [constructor] {A B C : Type*} {f g : A →* ppmap B C} (p : Πa, f a ~* g a)
    (q : p pt ⬝* phomotopy_of_eq (respect_pt g) = phomotopy_of_eq (respect_pt f))
    : f ~* g :=
  begin
    apply phomotopy.mk (λa, eq_of_phomotopy (p a)),
    apply eq_of_fn_eq_fn (pmap_eq_equiv _ _), esimp [pmap_eq_equiv],
    refine !phomotopy_of_eq_con ⬝ _,
    refine !phomotopy_of_eq_of_phomotopy ◾** idp ⬝ q,
  end

  /- properties of ppmap, the pointed type of pointed maps -/
  definition pcompose_pconst [constructor] (f : B →* C) : f ∘* pconst A B ~* pconst A C :=
  phomotopy.mk (λa, respect_pt f) (idp_con _)⁻¹

  definition pconst_pcompose [constructor] (f : A →* B) : pconst B C ∘* f ~* pconst A C :=
  phomotopy.mk (λa, rfl) !ap_constant⁻¹

  definition ppcompose_left [constructor] (g : B →* C) : ppmap A B →* ppmap A C :=
  pmap.mk (pcompose g) (eq_of_phomotopy (pcompose_pconst g))

  definition ppcompose_right [constructor] (f : A →* B) : ppmap B C →* ppmap A C :=
  pmap.mk (λg, g ∘* f) (eq_of_phomotopy (pconst_pcompose f))

  /- TODO: give construction using pequiv.MK, which computes better (see comment for a start of the proof), rename to ppmap_pequiv_ppmap_right -/
  definition pequiv_ppcompose_left [constructor] (g : B ≃* C) : ppmap A B ≃* ppmap A C :=
  pequiv.MK' (ppcompose_left g) (ppcompose_left g⁻¹ᵉ*)
    begin intro f, apply eq_of_phomotopy, apply pinv_pcompose_cancel_left end
    begin intro f, apply eq_of_phomotopy, apply pcompose_pinv_cancel_left end
  -- pequiv.MK (ppcompose_left g) (ppcompose_left g⁻¹ᵉ*)
  --   abstract begin
  --     apply phomotopy_mk_ppmap (pinv_pcompose_cancel_left g), esimp,
  --     refine !trans_refl ⬝ _,
  --     refine _ ⬝ (!phomotopy_of_eq_con ⬝ (!phomotopy_of_eq_pcompose_left ⬝
  --       ap (pwhisker_left _) !phomotopy_of_eq_of_phomotopy) ◾** !phomotopy_of_eq_of_phomotopy)⁻¹,

  --   end end
  --   abstract begin
  --     exact sorry
  --   end end

  definition pequiv_ppcompose_right [constructor] (f : A ≃* B) : ppmap B C ≃* ppmap A C :=
  begin
    fapply pequiv.MK',
    { exact ppcompose_right f },
    { exact ppcompose_right f⁻¹ᵉ* },
    { intro g, apply eq_of_phomotopy, apply pcompose_pinv_cancel_right },
    { intro g, apply eq_of_phomotopy, apply pinv_pcompose_cancel_right },
  end

  definition loop_ppmap_commute (A B : Type*) : Ω(ppmap A B) ≃* (ppmap A (Ω B)) :=
    pequiv_of_equiv
      (calc Ω(ppmap A B) ≃ (pconst A B ~* pconst A B)                       : pmap_eq_equiv _ _
                     ... ≃ Σ(p : pconst A B ~ pconst A B), p pt ⬝ rfl = rfl : phomotopy.sigma_char
                     ... ≃ (A →* Ω B)                                       : pmap.sigma_char)
      (by reflexivity)

  definition papply [constructor] {A : Type*} (B : Type*) (a : A) : ppmap A B →* B :=
  pmap.mk (λ(f : A →* B), f a) idp

  definition papply_pcompose [constructor] {A : Type*} (B : Type*) (a : A) : ppmap A B →* B :=
  pmap.mk (λ(f : A →* B), f a) idp

  definition ppmap_pbool_pequiv [constructor] (B : Type*) : ppmap pbool B ≃* B :=
  begin
    fapply pequiv.MK',
    { exact papply B tt },
    { exact pbool_pmap },
    { intro f, fapply eq_of_phomotopy, fapply phomotopy.mk,
      { intro b, cases b, exact !respect_pt⁻¹, reflexivity },
      { exact !con.left_inv }},
    { intro b, reflexivity },
  end

  definition papn_pt [constructor] (n : ℕ) (A B : Type*) : ppmap A B →* ppmap (Ω[n] A) (Ω[n] B) :=
  pmap.mk (λf, apn n f) (eq_of_phomotopy !apn_pconst)

  definition papn_fun [constructor] {n : ℕ} {A : Type*} (B : Type*) (p : Ω[n] A) :
    ppmap A B →* Ω[n] B :=
  papply _ p ∘* papn_pt n A B

  definition pconst_pcompose_pconst (A B C : Type*) :
    pconst_pcompose (pconst A B) = pcompose_pconst (pconst B C) :=
  idp

  definition pconst_pcompose_phomotopy_pconst {A B C : Type*} {f : A →* B} (p : f ~* pconst A B) :
    pconst_pcompose f = pwhisker_left (pconst B C) p ⬝* pcompose_pconst (pconst B C) :=
  begin
    assert H : Π(p : pconst A B ~* f),
      pconst_pcompose f = pwhisker_left (pconst B C) p⁻¹* ⬝* pcompose_pconst (pconst B C),
    { intro p, induction p using phomotopy_rec_idp, reflexivity },
    refine H p⁻¹* ⬝ ap (pwhisker_left _) !symm_symm ◾** idp,
  end

  definition passoc_pconst_right {A B C D : Type*} (h : C →* D) (g : B →* C) :
    passoc h g (pconst A B) ⬝* (pwhisker_left h (pcompose_pconst g) ⬝* pcompose_pconst h) =
    pcompose_pconst (h ∘* g) :=
  begin
    fapply phomotopy_eq,
    { intro a, exact !idp_con },
    { induction h with h h₀, induction g with g g₀, induction D with D d₀, induction C with C c₀,
      esimp at *, induction g₀, induction h₀, reflexivity }
  end

  definition passoc_pconst_middle {A A' B B' : Type*} (g : B →* B') (f : A' →* A) :
    passoc g (pconst A B) f ⬝* (pwhisker_left g (pconst_pcompose f) ⬝* pcompose_pconst g) =
    pwhisker_right f (pcompose_pconst g) ⬝* pconst_pcompose f :=
  begin
    fapply phomotopy_eq,
    { intro a, exact !idp_con ⬝ !idp_con },
    { induction g with g g₀, induction f with f f₀, induction B' with D d₀, induction A with C c₀,
      esimp at *, induction g₀, induction f₀, reflexivity }
  end

  definition passoc_pconst_left {A B C D : Type*} (g : B →* C) (f : A →* B) :
    phsquare (passoc (pconst C D) g f) (pconst_pcompose f)
             (pwhisker_right f (pconst_pcompose g)) (pconst_pcompose (g ∘* f)) :=
  begin
    fapply phomotopy_eq,
    { intro a, exact !idp_con },
    { induction g with g g₀, induction f with f f₀, induction C with C c₀, induction B with B b₀,
      esimp at *, induction g₀, induction f₀, reflexivity }
  end

  definition ppcompose_left_pcompose [constructor] {A B C D : Type*} (h : C →* D) (g : B →* C) :
    @ppcompose_left A _ _ (h ∘* g) ~* ppcompose_left h ∘* ppcompose_left g :=
  begin
    fapply phomotopy_mk_ppmap,
    { exact passoc h g },
    { refine idp ◾** (!phomotopy_of_eq_con ⬝
        (ap phomotopy_of_eq !pcompose_left_eq_of_phomotopy ⬝ !phomotopy_of_eq_of_phomotopy) ◾**
        !phomotopy_of_eq_of_phomotopy) ⬝ _ ⬝ !phomotopy_of_eq_of_phomotopy⁻¹,
      exact passoc_pconst_right h g }
  end

  definition ppcompose_right_pcompose [constructor] {A B C D : Type*} (g : B →* C) (f : A →* B) :
    @ppcompose_right _ _ D (g ∘* f) ~* ppcompose_right f ∘* ppcompose_right g :=
  begin
    symmetry,
    fapply phomotopy_mk_ppmap,
    { intro h, exact passoc h g f },
    { refine idp ◾** !phomotopy_of_eq_of_phomotopy ⬝ _ ⬝ (!phomotopy_of_eq_con ⬝
        (ap phomotopy_of_eq !pcompose_right_eq_of_phomotopy ⬝ !phomotopy_of_eq_of_phomotopy) ◾** !phomotopy_of_eq_of_phomotopy)⁻¹,
      exact passoc_pconst_left g f }
  end

  definition ppcompose_left_ppcompose_right {A A' B B' : Type*} (g : B →* B') (f : A' →* A) :
    psquare (ppcompose_left g) (ppcompose_left g) (ppcompose_right f) (ppcompose_right f) :=
  begin
    fapply phomotopy_mk_ppmap,
    { intro h, exact passoc g h f },
    { refine idp ◾** (!phomotopy_of_eq_con ⬝
        (ap phomotopy_of_eq !pcompose_left_eq_of_phomotopy ⬝ !phomotopy_of_eq_of_phomotopy) ◾**
        !phomotopy_of_eq_of_phomotopy) ⬝ _ ⬝ (!phomotopy_of_eq_con ⬝
        (ap phomotopy_of_eq !pcompose_right_eq_of_phomotopy ⬝ !phomotopy_of_eq_of_phomotopy) ◾**
        !phomotopy_of_eq_of_phomotopy)⁻¹,
      apply passoc_pconst_middle }
  end

  definition pcompose_pconst_phomotopy {A B C : Type*} {f f' : B →* C} (p : f ~* f') :
    pwhisker_right (pconst A B) p ⬝* pcompose_pconst f' = pcompose_pconst f :=
  begin
    fapply phomotopy_eq,
    { intro a, exact to_homotopy_pt p },
    { induction p using phomotopy_rec_idp, induction C with C c₀, induction f with f f₀,
      esimp at *, induction f₀, reflexivity }
  end

  definition pid_pconst (A B : Type*) : pcompose_pconst (pid B) = pid_pcompose (pconst A B) :=
  by reflexivity

  definition pid_pconst_pcompose {A B C : Type*} (f : A →* B) :
    phsquare (pid_pcompose (pconst B C ∘* f))
             (pcompose_pconst (pid C))
             (pwhisker_left (pid C) (pconst_pcompose f))
             (pconst_pcompose f) :=
  begin
    fapply phomotopy_eq,
    { reflexivity },
    { induction f with f f₀, induction B with B b₀, esimp at *, induction f₀, reflexivity }
  end

  definition ppcompose_left_pconst [constructor] (A B C : Type*) :
    @ppcompose_left A _ _ (pconst B C) ~* pconst (ppmap A B) (ppmap A C) :=
  begin
    fapply phomotopy_mk_ppmap,
    { exact pconst_pcompose },
    { refine idp ◾** !phomotopy_of_eq_idp ⬝ !phomotopy_of_eq_of_phomotopy⁻¹ }
  end

  definition ppcompose_left_phomotopy [constructor] {A B C : Type*} {g g' : B →* C} (p : g ~* g') :
    @ppcompose_left A _ _ g ~* ppcompose_left g' :=
  begin
    induction p using phomotopy_rec_idp,
    reflexivity
  end

  definition ppcompose_left_phomotopy_refl {A B C : Type*} (g : B →* C) :
    ppcompose_left_phomotopy (phomotopy.refl g) = phomotopy.refl (@ppcompose_left A _ _ g) :=
  !phomotopy_rec_idp_refl

    /- a more explicit proof of ppcompose_left_phomotopy, which might be useful if we need to prove properties about it
    -/
    -- fapply phomotopy_mk_ppmap,
    -- { intro f, exact pwhisker_right f p },
    -- { refine ap (λx, _ ⬝* x) !phomotopy_of_eq_of_phomotopy ⬝ _ ⬝ !phomotopy_of_eq_of_phomotopy⁻¹,
    --   exact pcompose_pconst_phomotopy p }

  definition ppcompose_right_phomotopy [constructor] {A B C : Type*} {f f' : A →* B} (p : f ~* f') :
    @ppcompose_right _ _ C f ~* ppcompose_right f' :=
  begin
    induction p using phomotopy_rec_idp,
    reflexivity
  end

  definition pppcompose [constructor] (A B C : Type*) : ppmap B C →* ppmap (ppmap A B) (ppmap A C) :=
  pmap.mk ppcompose_left (eq_of_phomotopy !ppcompose_left_pconst)

  section psquare

  variables {A' A₀₀ A₂₀ A₄₀ A₀₂ A₂₂ A₄₂ A₀₄ A₂₄ A₄₄ : Type*}
            {f₁₀ f₁₀' : A₀₀ →* A₂₀} {f₃₀ : A₂₀ →* A₄₀}
            {f₀₁ f₀₁' : A₀₀ →* A₀₂} {f₂₁ f₂₁' : A₂₀ →* A₂₂} {f₄₁ : A₄₀ →* A₄₂}
            {f₁₂ f₁₂' : A₀₂ →* A₂₂} {f₃₂ : A₂₂ →* A₄₂}
            {f₀₃ : A₀₂ →* A₀₄} {f₂₃ : A₂₂ →* A₂₄} {f₄₃ : A₄₂ →* A₄₄}
            {f₁₄ : A₀₄ →* A₂₄} {f₃₄ : A₂₄ →* A₄₄}

  definition ppcompose_left_psquare {A : Type*} (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) :
    psquare (@ppcompose_left A _ _ f₁₀) (ppcompose_left f₁₂)
            (ppcompose_left f₀₁) (ppcompose_left f₂₁) :=
  !ppcompose_left_pcompose⁻¹* ⬝* ppcompose_left_phomotopy p ⬝* !ppcompose_left_pcompose

  definition ppcompose_right_psquare {A : Type*} (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) :
    psquare (@ppcompose_right _ _ A f₁₂) (ppcompose_right f₁₀)
            (ppcompose_right f₂₁) (ppcompose_right f₀₁) :=
  !ppcompose_right_pcompose⁻¹* ⬝* ppcompose_right_phomotopy p⁻¹* ⬝* !ppcompose_right_pcompose

  definition trans_phomotopy_hconcat {f₀₁' f₀₁''}
    (q₂ : f₀₁'' ~* f₀₁') (q₁ : f₀₁' ~* f₀₁) (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) :
    (q₂ ⬝* q₁) ⬝ph* p = q₂ ⬝ph* q₁ ⬝ph* p :=
  idp ◾** (ap (pwhisker_left f₁₂) !trans_symm ⬝ !pwhisker_left_trans) ⬝ !trans_assoc⁻¹

  definition symm_phomotopy_hconcat {f₀₁'} (q : f₀₁ ~* f₀₁')
    (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) : q⁻¹* ⬝ph* p = p ⬝* pwhisker_left f₁₂ q :=
  idp ◾** ap (pwhisker_left f₁₂) !symm_symm

  definition refl_phomotopy_hconcat (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) : phomotopy.rfl ⬝ph* p = p :=
  idp ◾** (ap (pwhisker_left _) !refl_symm ⬝ !pwhisker_left_refl) ⬝ !trans_refl

  local attribute phomotopy.rfl [reducible]
  theorem pwhisker_left_phomotopy_hconcat {f₀₁'} (r : f₀₁' ~* f₀₁)
    (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) (q : psquare f₁₂ f₁₄ f₀₃ f₂₃) :
    pwhisker_left f₀₃ r ⬝ph* (p ⬝v* q) = (r ⬝ph* p) ⬝v* q :=
  by induction r using phomotopy_rec_idp; rewrite [pwhisker_left_refl, +refl_phomotopy_hconcat]

  theorem pvcompose_pwhisker_left {f₀₁'} (r : f₀₁ ~* f₀₁')
    (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) (q : psquare f₁₂ f₁₄ f₀₃ f₂₃) :
    (p ⬝v* q) ⬝* (pwhisker_left f₁₄ (pwhisker_left f₀₃ r)) = (p ⬝* pwhisker_left f₁₂ r) ⬝v* q :=
  by induction r using phomotopy_rec_idp; rewrite [+pwhisker_left_refl, + trans_refl]

  definition phconcat2 {p p' : psquare f₁₀ f₁₂ f₀₁ f₂₁} {q q' : psquare f₃₀ f₃₂ f₂₁ f₄₁}
    (r : p = p') (s : q = q') : p ⬝h* q = p' ⬝h* q' :=
  ap011 phconcat r s

  definition pvconcat2 {p p' : psquare f₁₀ f₁₂ f₀₁ f₂₁} {q q' : psquare f₁₂ f₁₄ f₀₃ f₂₃}
    (r : p = p') (s : q = q') : p ⬝v* q = p' ⬝v* q' :=
  ap011 pvconcat r s

  definition phinverse2 {f₁₀ : A₀₀ ≃* A₂₀} {f₁₂ : A₀₂ ≃* A₂₂} {p p' : psquare f₁₀ f₁₂ f₀₁ f₂₁}
    (r : p = p') : p⁻¹ʰ* = p'⁻¹ʰ* :=
  ap phinverse r

  definition pvinverse2 {f₀₁ : A₀₀ ≃* A₀₂} {f₂₁ : A₂₀ ≃* A₂₂} {p p' : psquare f₁₀ f₁₂ f₀₁ f₂₁}
    (r : p = p') : p⁻¹ᵛ* = p'⁻¹ᵛ* :=
  ap pvinverse r

  definition phomotopy_hconcat2 {q q' : f₀₁' ~* f₀₁} {p p' : psquare f₁₀ f₁₂ f₀₁ f₂₁}
    (r : q = q') (s : p = p') : q ⬝ph* p = q' ⬝ph* p' :=
  ap011 phomotopy_hconcat r s

  definition hconcat_phomotopy2 {p p' : psquare f₁₀ f₁₂ f₀₁ f₂₁} {q q' : f₂₁' ~* f₂₁}
    (r : p = p') (s : q = q') : p ⬝hp* q = p' ⬝hp* q' :=
  ap011 hconcat_phomotopy r s

  definition phomotopy_vconcat2 {q q' : f₁₀' ~* f₁₀} {p p' : psquare f₁₀ f₁₂ f₀₁ f₂₁}
    (r : q = q') (s : p = p') : q ⬝pv* p = q' ⬝pv* p' :=
  ap011 phomotopy_vconcat r s

  definition vconcat_phomotopy2 {p p' : psquare f₁₀ f₁₂ f₀₁ f₂₁} {q q' : f₁₂' ~* f₁₂}
    (r : p = p') (s : q = q') : p ⬝vp* q = p' ⬝vp* q' :=
  ap011 vconcat_phomotopy r s

  -- for consistency, should there be a second star here?
  infix ` ◾h* `:79 := phconcat2
  infix ` ◾v* `:79 := pvconcat2
  infixl ` ◾hp* `:79 := hconcat_phomotopy2
  infixr ` ◾ph* `:79 := phomotopy_hconcat2
  infixl ` ◾vp* `:79 := vconcat_phomotopy2
  infixr ` ◾pv* `:79 := phomotopy_vconcat2
  postfix `⁻²ʰ*`:(max+1) := phinverse2
  postfix `⁻²ᵛ*`:(max+1) := pvinverse2

  end psquare

  variables {X X' Y Y' Z : Type*}
  definition pap1 [constructor] (X Y : Type*) : ppmap X Y →* ppmap (Ω X) (Ω Y) :=
  pmap.mk ap1 (eq_of_phomotopy !ap1_pconst)

  definition ap1_gen_const {A B : Type} {a₁ a₂ : A} (b : B) (p : a₁ = a₂) :
    ap1_gen (const A b) idp idp p = idp :=
  ap1_gen_idp_left (const A b) p ⬝ ap_constant p b

  definition ap1_gen_compose_const_left
    {A B C : Type} (c : C) (f : A → B) {a₁ a₂ : A} (p : a₁ = a₂) :
    ap1_gen_compose (const B c) f idp idp idp idp p ⬝
    ap1_gen_const c (ap1_gen f idp idp p) =
    ap1_gen_const c p :=
  begin induction p, reflexivity end

  definition ap1_gen_compose_const_right
    {A B C : Type} (g : B → C) (b : B) {a₁ a₂ : A} (p : a₁ = a₂) :
    ap1_gen_compose g (const A b) idp idp idp idp p ⬝
    ap (ap1_gen g idp idp) (ap1_gen_const b p) =
    ap1_gen_const (g b) p :=
  begin induction p, reflexivity end

  definition ap1_pcompose_pconst_left {A B C : Type*} (f : A →* B) :
    phsquare (ap1_pcompose (pconst B C) f)
             (ap1_pconst A C)
             (ap1_phomotopy (pconst_pcompose f))
             (pwhisker_right (Ω→ f) (ap1_pconst B C) ⬝* pconst_pcompose (Ω→ f)) :=
  begin
    induction A with A a₀, induction B with B b₀, induction C with C c₀, induction f with f f₀,
    esimp at *, induction f₀,
    refine idp ◾** !trans_refl ⬝ _ ⬝ !refl_trans⁻¹ ⬝ !ap1_phomotopy_refl⁻¹ ◾** idp,
    fapply phomotopy_eq,
    { exact ap1_gen_compose_const_left c₀ f },
    { reflexivity }
  end

  definition ap1_pcompose_pconst_right {A B C : Type*} (g : B →* C) :
    phsquare (ap1_pcompose g (pconst A B))
             (ap1_pconst A C)
             (ap1_phomotopy (pcompose_pconst g))
             (pwhisker_left (Ω→ g) (ap1_pconst A B) ⬝* pcompose_pconst (Ω→ g)) :=
  begin
    induction A with A a₀, induction B with B b₀, induction C with C c₀, induction g with g g₀,
    esimp at *, induction g₀,
    refine idp ◾** !trans_refl ⬝ _ ⬝ !refl_trans⁻¹ ⬝ !ap1_phomotopy_refl⁻¹ ◾** idp,
    fapply phomotopy_eq,
    { exact ap1_gen_compose_const_right g b₀ },
    { reflexivity }
  end

  definition pap1_natural_left [constructor] (f : X' →* X) :
    psquare (pap1 X Y) (pap1 X' Y) (ppcompose_right f) (ppcompose_right (Ω→ f)) :=
  begin
    fapply phomotopy_mk_ppmap,
    { intro g, exact !ap1_pcompose⁻¹* },
    { refine idp ◾** (ap phomotopy_of_eq (!ap1_eq_of_phomotopy  ◾ idp ⬝ !eq_of_phomotopy_trans⁻¹) ⬝
      !phomotopy_of_eq_of_phomotopy)  ⬝ _ ⬝ (ap phomotopy_of_eq (!pcompose_right_eq_of_phomotopy ◾
      idp ⬝ !eq_of_phomotopy_trans⁻¹) ⬝ !phomotopy_of_eq_of_phomotopy)⁻¹,
      apply symm_trans_eq_of_eq_trans, exact (ap1_pcompose_pconst_left f)⁻¹ }
  end

  definition pap1_natural_right [constructor] (f : Y →* Y') :
    psquare (pap1 X Y) (pap1 X Y') (ppcompose_left f) (ppcompose_left (Ω→ f)) :=
  begin
    fapply phomotopy_mk_ppmap,
    { intro g, exact !ap1_pcompose⁻¹* },
    { refine idp ◾** (ap phomotopy_of_eq (!ap1_eq_of_phomotopy  ◾ idp ⬝ !eq_of_phomotopy_trans⁻¹) ⬝
      !phomotopy_of_eq_of_phomotopy)  ⬝ _ ⬝ (ap phomotopy_of_eq (!pcompose_left_eq_of_phomotopy ◾
      idp ⬝ !eq_of_phomotopy_trans⁻¹) ⬝ !phomotopy_of_eq_of_phomotopy)⁻¹,
      apply symm_trans_eq_of_eq_trans, exact (ap1_pcompose_pconst_right f)⁻¹ }
  end

  open sigma.ops prod
  definition pequiv.sigma_char {A B : Type*} :
    (A ≃* B) ≃ Σ(f : A →* B), (Σ(g : B →* A), f ∘* g ~* pid B) × (Σ(h : B →* A), h ∘* f ~* pid A) :=
  begin
    fapply equiv.MK,
    { intro f, exact ⟨f, (⟨pequiv.to_pinv1 f, pequiv.pright_inv f⟩,
                          ⟨pequiv.to_pinv2 f, pequiv.pleft_inv f⟩)⟩, },
    { intro f, exact pequiv.mk' f.1 (pr1 f.2).1 (pr2 f.2).1 (pr1 f.2).2 (pr2 f.2).2 },
    { intro f, induction f with f v, induction v with hl hr, induction hl, induction hr,
      reflexivity },
    { intro f, induction f, reflexivity }
  end

  definition is_contr_pright_inv (f : A ≃* B) : is_contr (Σ(g : B →* A), f ∘* g ~* pid B) :=
  begin
    fapply is_trunc_equiv_closed,
      { exact !fiber.sigma_char ⬝e sigma_equiv_sigma_right (λg, !pmap_eq_equiv) },
    fapply is_contr_fiber_of_is_equiv,
    exact pequiv.to_is_equiv (pequiv_ppcompose_left f)
  end

  definition is_contr_pleft_inv (f : A ≃* B) : is_contr (Σ(h : B →* A), h ∘* f ~* pid A) :=
  begin
    fapply is_trunc_equiv_closed,
      { exact !fiber.sigma_char ⬝e sigma_equiv_sigma_right (λg, !pmap_eq_equiv) },
    fapply is_contr_fiber_of_is_equiv,
    exact pequiv.to_is_equiv (pequiv_ppcompose_right f)
  end

  definition pequiv_eq_equiv (f g : A ≃* B) : (f = g) ≃ f ~* g :=
  have Π(f : A →* B), is_prop ((Σ(g : B →* A), f ∘* g ~* pid B) × (Σ(h : B →* A), h ∘* f ~* pid A)),
  begin
    intro f, apply is_prop_of_imp_is_contr, intro v,
    let f' := pequiv.sigma_char⁻¹ᵉ ⟨f, v⟩,
    apply is_trunc_prod, exact is_contr_pright_inv f', exact is_contr_pleft_inv f'
  end,
  calc (f = g) ≃ (pequiv.sigma_char f = pequiv.sigma_char g)
                 : eq_equiv_fn_eq pequiv.sigma_char f g
          ...  ≃ (f = g :> (A →* B)) : subtype_eq_equiv
          ...  ≃ (f ~* g) : pmap_eq_equiv f g

  definition pequiv_eq {f g : A ≃* B} (H : f ~* g) : f = g :=
  (pequiv_eq_equiv f g)⁻¹ᵉ H

  open algebra
  definition pequiv_of_isomorphism_of_eq {G₁ G₂ : Group} (p : G₁ = G₂) :
    pequiv_of_isomorphism (isomorphism_of_eq p) = pequiv_of_eq (ap pType_of_Group p) :=
  begin
    induction p,
    apply pequiv_eq,
    fapply phomotopy.mk,
    { intro g, reflexivity },
    { apply is_prop.elim }
  end

end pointed
