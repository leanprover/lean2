/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Mike Shulman

Ported from Coq HoTT
Theorems about fibers
-/

import .sigma .eq .pi cubical.squareover .pointed .eq
open equiv sigma sigma.ops eq pi pointed

structure fiber {A B : Type} (f : A → B) (b : B) :=
  (point : A)
  (point_eq : f point = b)

namespace fiber
  variables {A B : Type} {f : A → B} {b : B}

  protected definition sigma_char [constructor]
    (f : A → B) (b : B) : fiber f b ≃ (Σ(a : A), f a = b) :=
  begin
  fapply equiv.MK,
    {intro x, exact ⟨point x, point_eq x⟩},
    {intro x, exact (fiber.mk x.1 x.2)},
    {intro x, cases x, apply idp },
    {intro x, cases x, apply idp },
  end

  definition fiber_eq_equiv [constructor] (x y : fiber f b)
    : (x = y) ≃ (Σ(p : point x = point y), point_eq x = ap f p ⬝ point_eq y) :=
  begin
    apply equiv.trans,
      apply eq_equiv_fn_eq_of_equiv, apply fiber.sigma_char,
    apply equiv.trans,
      apply sigma_eq_equiv,
    apply sigma_equiv_sigma_right,
    intro p,
    apply eq_pathover_equiv_Fl,
  end

  definition fiber_eq {x y : fiber f b} (p : point x = point y)
    (q : point_eq x = ap f p ⬝ point_eq y) : x = y :=
  to_inv !fiber_eq_equiv ⟨p, q⟩

  definition fiber_pathover {X : Type} {A B : X → Type} {x₁ x₂ : X} {p : x₁ = x₂}
    {f : Πx, A x → B x} {b : Πx, B x} {v₁ : fiber (f x₁) (b x₁)} {v₂ : fiber (f x₂) (b x₂)}
    (q : point v₁ =[p] point v₂)
    (r : squareover B hrfl (pathover_idp_of_eq (point_eq v₁)) (pathover_idp_of_eq (point_eq v₂))
                           (apo f q) (apd b p))
    : v₁ =[p] v₂ :=
  begin
    apply pathover_of_fn_pathover_fn (λa, !fiber.sigma_char), esimp,
    fapply sigma_pathover: esimp,
    { exact q},
    { induction v₁ with a₁ p₁, induction v₂ with a₂ p₂, esimp at *, induction q, esimp at *,
      apply pathover_idp_of_eq, apply eq_of_vdeg_square, apply square_of_squareover_ids r}
  end

  open is_trunc
  definition fiber_pr1 (B : A → Type) (a : A) : fiber (pr1 : (Σa, B a) → A) a ≃ B a :=
  calc
    fiber pr1 a ≃ Σu, u.1 = a            : fiber.sigma_char
            ... ≃ Σa' (b : B a'), a' = a : sigma_assoc_equiv
            ... ≃ Σa' (p : a' = a), B a' : sigma_equiv_sigma_right (λa', !comm_equiv_nondep)
            ... ≃ Σu, B u.1              : sigma_assoc_equiv
            ... ≃ B a                    : !sigma_equiv_of_is_contr_left

  definition sigma_fiber_equiv (f : A → B) : (Σb, fiber f b) ≃ A :=
  calc
    (Σb, fiber f b) ≃ Σb a, f a = b : sigma_equiv_sigma_right (λb, !fiber.sigma_char)
                ... ≃ Σa b, f a = b : sigma_comm_equiv
                ... ≃ A             : sigma_equiv_of_is_contr_right

  definition is_pointed_fiber [instance] [constructor] (f : A → B) (a : A)
    : pointed (fiber f (f a)) :=
  pointed.mk (fiber.mk a idp)

  definition pointed_fiber [constructor] (f : A → B) (a : A) : Type* :=
  pointed.Mk (fiber.mk a (idpath (f a)))

  definition is_trunc_fun [reducible] (n : ℕ₋₂) (f : A → B) :=
  Π(b : B), is_trunc n (fiber f b)

  definition is_contr_fun [reducible] (f : A → B) := is_trunc_fun -2 f

  -- pre and post composition with equivalences
  open function
  variable (f)
  protected definition equiv_postcompose [constructor] {B' : Type} (g : B ≃ B') --[H : is_equiv g]
    (b : B) : fiber (g ∘ f) (g b) ≃ fiber f b :=
  calc
    fiber (g ∘ f) (g b) ≃ Σa : A, g (f a) = g b : fiber.sigma_char
                    ... ≃ Σa : A, f a = b       : begin
                                                    apply sigma_equiv_sigma_right, intro a,
                                                    apply equiv.symm, apply eq_equiv_fn_eq
                                                  end
                    ... ≃ fiber f b             : fiber.sigma_char

  protected definition equiv_precompose [constructor] {A' : Type} (g : A' ≃ A) --[H : is_equiv g]
    (b : B) : fiber (f ∘ g) b ≃ fiber f b :=
  calc
    fiber (f ∘ g) b ≃ Σa' : A', f (g a') = b   : fiber.sigma_char
                ... ≃ Σa : A, f a = b          : begin
                                                   apply sigma_equiv_sigma g,
                                                   intro a', apply erfl
                                                 end
                ... ≃ fiber f b                : fiber.sigma_char

end fiber

open unit is_trunc pointed

namespace fiber

  definition fiber_star_equiv [constructor] (A : Type) : fiber (λx : A, star) star ≃ A :=
  begin
    fapply equiv.MK,
    { intro f, cases f with a H, exact a },
    { intro a, apply fiber.mk a, reflexivity },
    { intro a, reflexivity },
    { intro f, cases f with a H, change fiber.mk a (refl star) = fiber.mk a H,
      rewrite [is_set.elim H (refl star)] }
  end

  definition fiber_const_equiv [constructor] (A : Type) (a₀ : A) (a : A)
    : fiber (λz : unit, a₀) a ≃ a₀ = a :=
  calc
    fiber (λz : unit, a₀) a
      ≃ Σz : unit, a₀ = a : fiber.sigma_char
  ... ≃ a₀ = a : sigma_unit_left

  -- the pointed fiber of a pointed map, which is the fiber over the basepoint
  open pointed
  definition pfiber [constructor] {X Y : Type*} (f : X →* Y) : Type* :=
  pointed.MK (fiber f pt) (fiber.mk pt !respect_pt)

  definition ppoint [constructor] {X Y : Type*} (f : X →* Y) : pfiber f →* X :=
  pmap.mk point idp

  definition pfiber.sigma_char [constructor] {A B : Type*} (f : A →* B)
    : pfiber f ≃* pointed.MK (Σa, f a = pt) ⟨pt, respect_pt f⟩ :=
  pequiv_of_equiv (fiber.sigma_char f pt) idp

  definition ppoint_sigma_char [constructor] {A B : Type*} (f : A →* B)
    : ppoint f ~* pmap.mk pr1 idp ∘* pfiber.sigma_char f :=
  !phomotopy.refl

  definition pfiber_pequiv_of_phomotopy {A B : Type*} {f g : A →* B} (h : f ~* g)
    : pfiber f ≃* pfiber g :=
  begin
    fapply pequiv_of_equiv,
    { refine (fiber.sigma_char f pt ⬝e _ ⬝e (fiber.sigma_char g pt)⁻¹ᵉ),
      apply sigma_equiv_sigma_right, intros a,
      apply equiv_eq_closed_left, apply (to_homotopy h) },
    { refine (fiber_eq rfl _),
      change (h pt)⁻¹ ⬝ respect_pt f = idp ⬝ respect_pt g,
      rewrite idp_con, apply inv_con_eq_of_eq_con, symmetry, exact (to_homotopy_pt h) }
  end

  definition transport_fiber_equiv [constructor] {A B : Type} (f : A → B) {b1 b2 : B} (p : b1 = b2)
    : fiber f b1 ≃ fiber f b2 :=
    calc fiber f b1 ≃ Σa, f a = b1 : fiber.sigma_char
               ...  ≃ Σa, f a = b2 : sigma_equiv_sigma_right (λa, equiv_eq_closed_right (f a) p)
               ...  ≃ fiber f b2   : fiber.sigma_char

  definition pequiv_postcompose {A B B' : Type*} (f : A →* B) (g : B ≃* B')
    : pfiber (g ∘* f) ≃* pfiber f :=
  begin
    fapply pequiv_of_equiv, esimp,
    refine transport_fiber_equiv (g ∘* f) (respect_pt g)⁻¹ ⬝e fiber.equiv_postcompose f g (Point B),
    esimp, apply (ap (fiber.mk (Point A))), refine !con.assoc ⬝ _, apply inv_con_eq_of_eq_con,
    rewrite [con.assoc, con.right_inv, con_idp, -ap_compose'], apply ap_con_eq_con
  end

  definition pequiv_precompose {A A' B : Type*} (f : A →* B) (g : A' ≃* A)
    : pfiber (f ∘* g) ≃* pfiber f :=
  begin
    fapply pequiv_of_equiv, esimp,
    refine fiber.equiv_precompose f g (Point B),
    esimp, apply (eq_of_fn_eq_fn (fiber.sigma_char _ _)), fapply sigma_eq: esimp,
    { apply respect_pt g },
    { apply eq_pathover_Fl' }
  end

  definition pfiber_pequiv_of_square {A B C D : Type*} {f : A →* B} {g : C →* D} (h : A ≃* C)
    (k : B ≃* D) (s : k ∘* f ~* g ∘* h) : pfiber f ≃* pfiber g :=
    calc pfiber f ≃* pfiber (k ∘* f) : pequiv_postcompose
              ... ≃* pfiber (g ∘* h) : pfiber_pequiv_of_phomotopy s
              ... ≃* pfiber g : pequiv_precompose

  definition pcompose_ppoint {A B : Type*} (f : A →* B) : f ∘* ppoint f ~* pconst (pfiber f) B :=
  begin
    fapply phomotopy.mk,
    { exact point_eq },
    { exact !idp_con⁻¹ }
  end

  definition point_fiber_eq {A B : Type} {f : A → B} {b : B} {x y : fiber f b}
    (p : point x = point y) (q : point_eq x = ap f p ⬝ point_eq y) :
    ap point (fiber_eq p q) = p :=
  begin
    induction x with a r, induction y with a' s, esimp at *, induction p,
    induction q using eq.rec_symm, induction s, reflexivity
  end

  definition fiber_eq_equiv_fiber {A B : Type} {f : A → B} {b : B} (x y : fiber f b) :
    x = y ≃ fiber (ap1_gen f (point_eq x) (point_eq y)) (idpath b) :=
  calc
    x = y ≃ fiber.sigma_char f b x = fiber.sigma_char f b y :
      eq_equiv_fn_eq_of_equiv (fiber.sigma_char f b) x y
      ... ≃ Σ(p : point x = point y), point_eq x =[p] point_eq y : sigma_eq_equiv
      ... ≃ Σ(p : point x = point y), (point_eq x)⁻¹ ⬝ ap f p ⬝ point_eq y = idp :
      sigma_equiv_sigma_right (λp,
      calc point_eq x =[p] point_eq y ≃ point_eq x = ap f p ⬝ point_eq y : eq_pathover_equiv_Fl
           ... ≃ ap f p ⬝ point_eq y = point_eq x : eq_equiv_eq_symm
           ... ≃ (point_eq x)⁻¹ ⬝ (ap f p ⬝ point_eq y) = idp : eq_equiv_inv_con_eq_idp
           ... ≃ (point_eq x)⁻¹ ⬝ ap f p ⬝ point_eq y = idp : equiv_eq_closed_left _ !con.assoc⁻¹)
      ... ≃ fiber (ap1_gen f (point_eq x) (point_eq y)) (idpath b) : fiber.sigma_char

  definition loop_pfiber [constructor] {A B : Type*} (f : A →* B) : Ω (pfiber f) ≃* pfiber (Ω→ f) :=
  pequiv_of_equiv (fiber_eq_equiv_fiber pt pt)
    begin
      induction f with f f₀, induction B with B b₀, esimp at (f,f₀), induction f₀, reflexivity
    end

  definition pfiber_loop_space {A B : Type*} (f : A →* B) : pfiber (Ω→ f) ≃* Ω (pfiber f) :=
  (loop_pfiber f)⁻¹ᵉ*

  definition point_fiber_eq_equiv_fiber {A B : Type} {f : A → B} {b : B} {x y : fiber f b}
    (p : x = y) : point (fiber_eq_equiv_fiber x y p) = ap1_gen point idp idp p :=
  by induction p; reflexivity

  lemma ppoint_loop_pfiber {A B : Type*} (f : A →* B) :
    ppoint (Ω→ f) ∘* loop_pfiber f ~* Ω→ (ppoint f) :=
  phomotopy.mk (point_fiber_eq_equiv_fiber)
    begin
     induction f with f f₀, induction B with B b₀, esimp at (f,f₀), induction f₀, reflexivity
    end

  lemma ppoint_loop_pfiber_inv {A B : Type*} (f : A →* B) :
    Ω→ (ppoint f) ∘* (loop_pfiber f)⁻¹ᵉ* ~* ppoint (Ω→ f) :=
  (phomotopy_pinv_right_of_phomotopy (ppoint_loop_pfiber f))⁻¹*

  lemma pfiber_pequiv_of_phomotopy_ppoint {A B : Type*} {f g : A →* B} (h : f ~* g)
    : ppoint g ∘* pfiber_pequiv_of_phomotopy h ~* ppoint f :=
  begin
    induction f with f f₀, induction g with g g₀, induction h with h h₀, induction B with B b₀,
    esimp at *, induction h₀, induction g₀,
    fapply phomotopy.mk,
    { reflexivity },
    { esimp [pfiber_pequiv_of_phomotopy], exact !point_fiber_eq⁻¹ }
  end

  lemma pequiv_postcompose_ppoint {A B B' : Type*} (f : A →* B) (g : B ≃* B')
    : ppoint f ∘* fiber.pequiv_postcompose f g ~* ppoint (g ∘* f) :=
  begin
    induction f with f f₀, induction g with g hg g₀, induction B with B b₀,
    induction B' with B' b₀', esimp at *, induction g₀, induction f₀,
    fapply phomotopy.mk,
    { reflexivity },
    { esimp [pequiv_postcompose], symmetry,
      refine !ap_compose⁻¹ ⬝ _, apply ap_constant }
  end

  lemma pequiv_precompose_ppoint {A A' B : Type*} (f : A →* B) (g : A' ≃* A)
    : ppoint f ∘* fiber.pequiv_precompose f g ~* g ∘* ppoint (f ∘* g) :=
  begin
    induction f with f f₀, induction g with g hg g₀, induction B with B b₀,
    induction A with A a₀', esimp at *, induction g₀, induction f₀,
    reflexivity,
  end

  definition pfiber_pequiv_of_square_ppoint {A B C D : Type*} {f : A →* B} {g : C →* D}
    (h : A ≃* C) (k : B ≃* D) (s : k ∘* f ~* g ∘* h)
    : ppoint g ∘* pfiber_pequiv_of_square h k s ~* h ∘* ppoint f :=
  begin
    refine !passoc⁻¹* ⬝* _,
    refine pwhisker_right _ !pequiv_precompose_ppoint ⬝* _,
    refine !passoc ⬝* _,
    apply pwhisker_left,
    refine !passoc⁻¹* ⬝* _,
    refine pwhisker_right _ !pfiber_pequiv_of_phomotopy_ppoint ⬝* _,
    apply pinv_right_phomotopy_of_phomotopy,
    refine !pequiv_postcompose_ppoint⁻¹*,
  end

  -- this breaks certain proofs if it is an instance
  definition is_trunc_fiber (n : ℕ₋₂) {A B : Type} (f : A → B) (b : B)
    [is_trunc n A] [is_trunc (n.+1) B] : is_trunc n (fiber f b) :=
  is_trunc_equiv_closed_rev n !fiber.sigma_char

  definition is_trunc_pfiber (n : ℕ₋₂) {A B : Type*} (f : A →* B)
    [is_trunc n A] [is_trunc (n.+1) B] : is_trunc n (pfiber f) :=
  is_trunc_fiber n f pt

  definition fiber_equiv_of_is_contr [constructor] {A B : Type} (f : A → B) (b : B) [is_contr B] :
    fiber f b ≃ A :=
  !fiber.sigma_char ⬝e !sigma_equiv_of_is_contr_right

  definition pfiber_pequiv_of_is_contr [constructor] {A B : Type*} (f : A →* B) [is_contr B] :
    pfiber f ≃* A :=
  pequiv_of_equiv (fiber_equiv_of_is_contr f pt) idp

end fiber

open function is_equiv

namespace fiber
  /- Theorem 4.7.6 -/
  variables {A : Type} {P Q : A → Type}
  variable (f : Πa, P a → Q a)

  definition fiber_total_equiv [constructor] {a : A} (q : Q a)
    : fiber (total f) ⟨a , q⟩ ≃ fiber (f a) q :=
  calc
    fiber (total f) ⟨a , q⟩
          ≃ Σ(w : Σx, P x), ⟨w.1 , f w.1 w.2 ⟩ = ⟨a , q⟩
            : fiber.sigma_char
      ... ≃ Σ(x : A), Σ(p : P x), ⟨x , f x p⟩ = ⟨a , q⟩
            : sigma_assoc_equiv
      ... ≃ Σ(x : A), Σ(p : P x), Σ(H : x = a), f x p =[H] q
            :
            begin
              apply sigma_equiv_sigma_right, intro x,
              apply sigma_equiv_sigma_right, intro p,
              apply sigma_eq_equiv
            end
      ... ≃ Σ(x : A), Σ(H : x = a), Σ(p : P x), f x p =[H] q
            :
            begin
              apply sigma_equiv_sigma_right, intro x,
              apply sigma_comm_equiv
            end
      ... ≃ Σ(w : Σx, x = a), Σ(p : P w.1), f w.1 p =[w.2] q
            : sigma_assoc_equiv
      ... ≃ Σ(p : P (center (Σx, x=a)).1), f (center (Σx, x=a)).1 p =[(center (Σx, x=a)).2] q
            : sigma_equiv_of_is_contr_left
      ... ≃ Σ(p : P a), f a p =[idpath a] q
            : equiv_of_eq idp
      ... ≃ Σ(p : P a), f a p = q
            :
            begin
              apply sigma_equiv_sigma_right, intro p,
              apply pathover_idp
            end
      ... ≃ fiber (f a) q
            : fiber.sigma_char

end fiber
