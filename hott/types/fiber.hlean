/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Mike Shulman

Ported from Coq HoTT
Theorems about fibers
-/

import .sigma .eq .pi cubical.squareover .pointed .eq
open equiv sigma sigma.ops eq pi pointed is_equiv is_trunc function unit

structure fiber {A B : Type} (f : A → B) (b : B) :=
  (point : A)
  (point_eq : f point = b)

variables {A B : Type} {f : A → B} {b : B}

namespace fiber

  protected definition sigma_char [constructor]
    (f : A → B) (b : B) : fiber f b ≃ (Σ(a : A), f a = b) :=
  begin
  fapply equiv.MK,
    {intro x, exact ⟨point x, point_eq x⟩},
    {intro x, exact (fiber.mk x.1 x.2)},
    {intro x, cases x, apply idp },
    {intro x, cases x, apply idp },
  end

  /- equality type of a fiber -/
  definition fiber_eq_equiv' [constructor] (x y : fiber f b)
    : (x = y) ≃ (Σ(p : point x = point y), point_eq x = ap f p ⬝ point_eq y) :=
  begin
    apply equiv.trans,
      apply eq_equiv_fn_eq, apply fiber.sigma_char,
    apply equiv.trans,
      apply sigma_eq_equiv,
    apply sigma_equiv_sigma_right,
    intro p,
    apply eq_pathover_equiv_Fl,
  end

  definition fiber_eq {x y : fiber f b} (p : point x = point y)
    (q : point_eq x = ap f p ⬝ point_eq y) : x = y :=
  to_inv !fiber_eq_equiv' ⟨p, q⟩

  definition fiber_eq_equiv [constructor] (x y : fiber f b) :
    (x = y) ≃ (Σ(p : point x = point y), point_eq x = ap f p ⬝ point_eq y) :=
  @equiv_change_inv _ _ (fiber_eq_equiv' x y) (λpq, fiber_eq pq.1 pq.2)
    begin intro pq, cases pq, reflexivity end

  definition point_fiber_eq {x y : fiber f b}
    (p : point x = point y) (q : point_eq x = ap f p ⬝ point_eq y) :
    ap point (fiber_eq p q) = p :=
  begin
    induction x with a r, induction y with a' s, esimp at *, induction p,
    induction q using eq.rec_symm, induction s, reflexivity
  end

  definition fiber_eq_equiv_fiber (x y : fiber f b) :
    x = y ≃ fiber (ap1_gen f (point_eq x) (point_eq y)) (idpath b) :=
  calc
    x = y ≃ fiber.sigma_char f b x = fiber.sigma_char f b y :
      eq_equiv_fn_eq (fiber.sigma_char f b) x y
      ... ≃ Σ(p : point x = point y), point_eq x =[p] point_eq y : sigma_eq_equiv
      ... ≃ Σ(p : point x = point y), (point_eq x)⁻¹ ⬝ ap f p ⬝ point_eq y = idp :
      sigma_equiv_sigma_right (λp,
      calc point_eq x =[p] point_eq y ≃ point_eq x = ap f p ⬝ point_eq y : eq_pathover_equiv_Fl
           ... ≃ ap f p ⬝ point_eq y = point_eq x : eq_equiv_eq_symm
           ... ≃ (point_eq x)⁻¹ ⬝ (ap f p ⬝ point_eq y) = idp : eq_equiv_inv_con_eq_idp
           ... ≃ (point_eq x)⁻¹ ⬝ ap f p ⬝ point_eq y = idp : equiv_eq_closed_left _ !con.assoc⁻¹)
      ... ≃ fiber (ap1_gen f (point_eq x) (point_eq y)) (idpath b) : fiber.sigma_char

  definition point_fiber_eq_equiv_fiber {x y : fiber f b}
    (p : x = y) : point (fiber_eq_equiv_fiber x y p) = ap1_gen point idp idp p :=
  by induction p; reflexivity

  definition fiber_eq_pr2 {x y : fiber f b}
    (p : x = y) : point_eq x = ap f (ap point p) ⬝ point_eq y :=
  begin induction p, exact !idp_con⁻¹ end

  definition fiber_eq_eta {x y : fiber f b}
    (p : x = y) : p = fiber_eq (ap point p) (fiber_eq_pr2 p) :=
  begin induction p, induction x with a q, induction q, reflexivity end

  definition fiber_eq_con {x y z : fiber f b}
    (p1 : point x = point y) (p2 : point y = point z)
    (q1 : point_eq x = ap f p1 ⬝ point_eq y) (q2 : point_eq y = ap f p2 ⬝ point_eq z) :
    fiber_eq p1 q1 ⬝ fiber_eq p2 q2 =
    fiber_eq (p1 ⬝ p2) (q1 ⬝ whisker_left (ap f p1) q2 ⬝ !con.assoc⁻¹ ⬝
                         whisker_right (point_eq z) (ap_con f p1 p2)⁻¹) :=
  begin
    induction x with a₁ r₁, induction y with a₂ r₂, induction z with a₃ r₃, esimp at *,
    induction q2 using eq.rec_symm, induction q1 using eq.rec_symm,
    induction p2, induction p1, induction r₃, reflexivity
  end

  definition fiber_eq2_equiv {x y : fiber f b}
    (p₁ p₂ : point x = point y) (q₁ : point_eq x = ap f p₁ ⬝ point_eq y)
    (q₂ : point_eq x = ap f p₂ ⬝ point_eq y) : (fiber_eq p₁ q₁ = fiber_eq p₂ q₂) ≃
    (Σ(r : p₁ = p₂), q₁ ⬝ whisker_right (point_eq y) (ap02 f r) = q₂) :=
  begin
    refine (eq_equiv_fn_eq (fiber_eq_equiv x y)⁻¹ᵉ _ _)⁻¹ᵉ ⬝e sigma_eq_equiv _ _ ⬝e _,
    apply sigma_equiv_sigma_right, esimp, intro r,
    refine !eq_pathover_equiv_square ⬝e _,
    refine eq_hconcat_equiv !ap_constant ⬝e hconcat_eq_equiv (ap_compose (λx, x ⬝ _) _ _) ⬝e _,
    refine !square_equiv_eq ⬝e _,
    exact eq_equiv_eq_closed idp (idp_con q₂)
  end

  definition fiber_eq2 {x y : fiber f b}
    {p₁ p₂ : point x = point y} {q₁ : point_eq x = ap f p₁ ⬝ point_eq y}
    {q₂ : point_eq x = ap f p₂ ⬝ point_eq y} (r : p₁ = p₂)
    (s : q₁ ⬝ whisker_right (point_eq y) (ap02 f r) = q₂) : (fiber_eq p₁ q₁ = fiber_eq p₂ q₂) :=
  (fiber_eq2_equiv p₁ p₂ q₁ q₂)⁻¹ᵉ ⟨r, s⟩

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

  definition is_trunc_fiber (n : ℕ₋₂) {A B : Type} (f : A → B) (b : B)
    [is_trunc n A] [is_trunc (n.+1) B] : is_trunc n (fiber f b) :=
  is_trunc_equiv_closed_rev n !fiber.sigma_char _

  definition is_contr_fiber_id (A : Type) (a : A) : is_contr (fiber (@id A) a) :=
  is_contr.mk (fiber.mk a idp)
    begin intro x, induction x with a p, esimp at p, cases p, reflexivity end

  /- the general functoriality between fibers -/
  -- todo: transpose the hsquare in fiber_functor?
  -- todo: show that the underlying map of fiber_equiv_of_square is fiber_functor
  definition fiber_functor [constructor] {A A' B B' : Type} {f : A → B} {f' : A' → B'}
    {b : B} {b' : B'} (g : A → A') (h : B → B') (H : hsquare g h f f') (p : h b = b')
    (x : fiber f b) : fiber f' b' :=
  fiber.mk (g (point x)) (H (point x) ⬝ ap h (point_eq x) ⬝ p)

  /- equivalences between fibers -/

  definition fiber_equiv_of_homotopy {A B : Type} {f g : A → B} (h : f ~ g) (b : B)
    : fiber f b ≃ fiber g b :=
  begin
    refine (fiber.sigma_char f b ⬝e _ ⬝e (fiber.sigma_char g b)⁻¹ᵉ),
    apply sigma_equiv_sigma_right, intros a,
    apply equiv_eq_closed_left, apply h
  end

  definition fiber_equiv_basepoint [constructor] {A B : Type} (f : A → B) {b1 b2 : B} (p : b1 = b2)
    : fiber f b1 ≃ fiber f b2 :=
    calc fiber f b1 ≃ Σa, f a = b1 : fiber.sigma_char
               ...  ≃ Σa, f a = b2 : sigma_equiv_sigma_right (λa, equiv_eq_closed_right (f a) p)
               ...  ≃ fiber f b2   : fiber.sigma_char


  definition fiber_pr1 (B : A → Type) (a : A) : fiber (pr1 : (Σa, B a) → A) a ≃ B a :=
  calc
    fiber pr1 a ≃ Σu, u.1 = a            : fiber.sigma_char
            ... ≃ Σa' (b : B a'), a' = a : sigma_assoc_equiv
            ... ≃ Σa' (p : a' = a), B a' : sigma_equiv_sigma_right (λa', !comm_equiv_nondep)
            ... ≃ Σu, B u.1              : sigma_assoc_equiv
            ... ≃ B a                    : sigma_equiv_of_is_contr_left _ _

  definition sigma_fiber_equiv (f : A → B) : (Σb, fiber f b) ≃ A :=
  calc
    (Σb, fiber f b) ≃ Σb a, f a = b : sigma_equiv_sigma_right (λb, !fiber.sigma_char)
                ... ≃ Σa b, f a = b : sigma_comm_equiv
                ... ≃ A             : sigma_equiv_of_is_contr_right _ _

  definition fiber_compose_equiv {A B C : Type} (g : B → C) (f : A → B) (c : C) :
    fiber (g ∘ f) c ≃ Σ(x : fiber g c), fiber f (point x) :=
  begin
    fapply equiv.MK,
    { intro x, exact ⟨fiber.mk (f (point x)) (point_eq x), fiber.mk (point x) idp⟩ },
    { intro x, exact fiber.mk (point x.2) (ap g (point_eq x.2) ⬝ point_eq x.1) },
    { intro x, induction x with x₁ x₂, induction x₁ with b p, induction x₂ with a q,
      induction p, esimp at q, induction q, reflexivity },
    { intro x, induction x with a p, induction p, reflexivity }
  end

  -- pre and post composition with equivalences
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

  definition fiber_equiv_of_square {A B C D : Type} {b : B} {d : D} {f : A → B} {g : C → D}
    (h : A ≃ C) (k : B ≃ D) (s : hsquare f g h k) (p : k b = d) : fiber f b ≃ fiber g d :=
    calc fiber f b ≃ fiber (k ∘ f) (k b) : fiber.equiv_postcompose
              ... ≃ fiber (k ∘ f) d : fiber_equiv_basepoint (k ∘ f) p
              ... ≃ fiber (g ∘ h) d : fiber_equiv_of_homotopy s d
              ... ≃ fiber g d : fiber.equiv_precompose

  definition fiber_equiv_of_triangle {A B C : Type} {b : B} {f : A → B} {g : C → B} (h : A ≃ C)
    (s : f ~ g ∘ h) : fiber f b ≃ fiber g b :=
  fiber_equiv_of_square h erfl s idp

  definition is_contr_fiber_equiv [instance] (f : A ≃ B) (b : B) : is_contr (fiber f b) :=
  is_contr_equiv_closed
    (fiber_equiv_of_homotopy (to_left_inv f)⁻¹ʰᵗʸ _ ⬝e fiber.equiv_postcompose f f⁻¹ᵉ b)
    !is_contr_fiber_id

  definition is_contr_fiber_of_is_equiv [instance] [is_equiv f] (b : B) : is_contr (fiber f b) :=
  is_contr_fiber_equiv (equiv.mk f _) b

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

  definition fiber_total_equiv [constructor] {P Q : A → Type} (f : Πa, P a → Q a) {a : A} (q : Q a)
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

  definition fiber_equiv_of_is_contr [constructor] {A B : Type} (f : A → B) (b : B)
    (H : is_contr B) : fiber f b ≃ A :=
  !fiber.sigma_char ⬝e sigma_equiv_of_is_contr_right _ _

  /- the pointed fiber of a pointed map, which is the fiber over the basepoint -/

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
    { exact fiber_equiv_of_homotopy h pt },
    { refine (fiber_eq rfl _),
      change (h pt)⁻¹ ⬝ respect_pt f = idp ⬝ respect_pt g,
      rewrite idp_con, apply inv_con_eq_of_eq_con, symmetry, exact (to_homotopy_pt h) }
  end

  definition pequiv_postcompose {A B B' : Type*} (f : A →* B) (g : B ≃* B')
    : pfiber (g ∘* f) ≃* pfiber f :=
  begin
    fapply pequiv_of_equiv, esimp,
    refine fiber_equiv_basepoint (g ∘* f) (respect_pt g)⁻¹ ⬝e fiber.equiv_postcompose f g (Point B),
    esimp, apply (ap (fiber.mk (Point A))), refine !con.assoc ⬝ _, apply inv_con_eq_of_eq_con,
    rewrite [▸*, con.assoc, con.right_inv, con_idp, ap_compose'],
    exact ap_con_eq_con (λ x, ap g⁻¹ᵉ* (ap g (pleft_inv' g x)⁻¹) ⬝ ap g⁻¹ᵉ* (pright_inv g (g x)) ⬝
      pleft_inv' g x) (respect_pt f)
  end

  definition pequiv_precompose {A A' B : Type*} (f : A →* B) (g : A' ≃* A)
    : pfiber (f ∘* g) ≃* pfiber f :=
  begin
    fapply pequiv_of_equiv, esimp,
    refine fiber.equiv_precompose f g (Point B),
    esimp, apply (inj (fiber.sigma_char _ _)), fapply sigma_eq: esimp,
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

  definition loop_pfiber [constructor] {A B : Type*} (f : A →* B) : Ω (pfiber f) ≃* pfiber (Ω→ f) :=
  pequiv_of_equiv (fiber_eq_equiv_fiber pt pt)
    begin
      induction f with f f₀, induction B with B b₀, esimp at (f,f₀), induction f₀, reflexivity
    end

  definition pfiber_loop_space {A B : Type*} (f : A →* B) : pfiber (Ω→ f) ≃* Ω (pfiber f) :=
  (loop_pfiber f)⁻¹ᵉ*

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
    { symmetry, rexact point_fiber_eq (idpath pt)
        (inv_con_eq_of_eq_con (idpath (h pt ⬝ (idp ⬝ point_eq (fiber.mk pt idp))))) }
  end

  lemma pequiv_postcompose_ppoint {A B B' : Type*} (f : A →* B) (g : B ≃* B')
    : ppoint f ∘* fiber.pequiv_postcompose f g ~* ppoint (g ∘* f) :=
  begin
    induction f with f f₀, induction g with g hg g₀, induction B with B b₀,
    induction B' with B' b₀', esimp at * ⊢, induction g₀, induction f₀,
    fapply phomotopy.mk,
    { reflexivity },
    { symmetry,
      refine !ap_compose⁻¹ ⬝ _, apply ap_constant }
  end

  lemma pequiv_precompose_ppoint {A A' B : Type*} (f : A →* B) (g : A' ≃* A)
    : ppoint f ∘* fiber.pequiv_precompose f g ~* g ∘* ppoint (f ∘* g) :=
  begin
    induction f with f f₀, induction g with g h₁ h₂ p₁ p₂, induction B with B b₀,
    induction g with g g₀, induction A with A a₀', esimp at *, induction g₀, induction f₀,
    reflexivity
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

  definition is_trunc_pfiber (n : ℕ₋₂) {A B : Type*} (f : A →* B)
    [is_trunc n A] [is_trunc (n.+1) B] : is_trunc n (pfiber f) :=
  is_trunc_fiber n f pt

  definition pfiber_pequiv_of_is_contr [constructor] {A B : Type*} (f : A →* B) (H : is_contr B) :
    pfiber f ≃* A :=
  pequiv_of_equiv (fiber_equiv_of_is_contr f pt H) idp

  definition pfiber_ppoint_equiv {A B : Type*} (f : A →* B) : pfiber (ppoint f) ≃ Ω B :=
  calc
    pfiber (ppoint f) ≃ Σ(x : pfiber f), ppoint f x = pt : fiber.sigma_char
      ... ≃ Σ(x : Σa, f a = pt), x.1 = pt : by exact sigma_equiv_sigma !fiber.sigma_char (λa, erfl)
      ... ≃ Σ(x : Σa, a = pt), f x.1 = pt : by exact !sigma_assoc_comm_equiv
      ... ≃ f pt = pt : by exact sigma_equiv_of_is_contr_left _ _
      ... ≃ Ω B : by exact !equiv_eq_closed_left !respect_pt

  definition pfiber_ppoint_pequiv {A B : Type*} (f : A →* B) : pfiber (ppoint f) ≃* Ω B :=
  pequiv_of_equiv (pfiber_ppoint_equiv f) !con.left_inv

  definition pfiber_ppoint_equiv_eq {A B : Type*} {f : A →* B} {a : A} (p : f a = pt)
    (q : ppoint f (fiber.mk a p) = pt) :
    pfiber_ppoint_equiv f (fiber.mk (fiber.mk a p) q) = (respect_pt f)⁻¹ ⬝ ap f q⁻¹ ⬝ p :=
  begin
    refine _ ⬝ !con.assoc⁻¹,
    apply whisker_left,
    refine eq_transport_Fl _ _ ⬝ _,
    apply whisker_right,
    refine inverse2 !ap_inv ⬝ !inv_inv ⬝ _,
    refine ap_compose f pr₁ _ ⬝ ap02 f !ap_pr1_center_eq_sigma_eq',
  end

  definition pfiber_ppoint_equiv_inv_eq {A B : Type*} (f : A →* B) (p : Ω B) :
    (pfiber_ppoint_equiv f)⁻¹ᵉ p = fiber.mk (fiber.mk pt (respect_pt f ⬝ p)) idp :=
  begin
    apply inv_eq_of_eq,
    refine _ ⬝ !pfiber_ppoint_equiv_eq⁻¹,
    exact !inv_con_cancel_left⁻¹
  end

  definition loopn_pfiber [constructor] {A B : Type*} (n : ℕ) (f : A →* B) :
    Ω[n] (pfiber f) ≃* pfiber (Ω→[n] f) :=
  begin
    induction n with n IH, reflexivity, exact loop_pequiv_loop IH ⬝e* loop_pfiber (Ω→[n] f),
  end

  definition is_contr_pfiber_pid (A : Type*) : is_contr (pfiber (pid A)) :=
  by exact is_contr_fiber_id A pt

  definition pfiber_functor [constructor] {A A' B B' : Type*} {f : A →* B} {f' : A' →* B'}
    (g : A →* A') (h : B →* B') (H : psquare g h f f') : pfiber f →* pfiber f' :=
  pmap.mk (fiber_functor g h H (respect_pt h))
    begin
      fapply fiber_eq,
        exact respect_pt g,
        exact !con.assoc ⬝ to_homotopy_pt H
    end

  definition ppoint_natural {A A' B B' : Type*} {f : A →* B} {f' : A' →* B'}
    (g : A →* A') (h : B →* B') (H : psquare g h f f') :
    psquare (ppoint f) (ppoint f') (pfiber_functor g h H) g :=
  begin
    fapply phomotopy.mk,
    { intro x, reflexivity },
    { refine !idp_con ⬝ _ ⬝ !idp_con⁻¹, esimp, apply point_fiber_eq }
  end

  /- A less commonly used pointed fiber with basepoint (f a) for some a in the domain of f -/
  definition pointed_fiber [constructor] (f : A → B) (a : A) : Type* :=
  pointed.Mk (fiber.mk a (idpath (f a)))

end fiber
open fiber

/- A function is truncated if it has truncated fibers -/
definition is_trunc_fun [reducible] (n : ℕ₋₂) (f : A → B) :=
Π(b : B), is_trunc n (fiber f b)

definition is_contr_fun [reducible] (f : A → B) := is_trunc_fun -2 f

definition is_trunc_fun_id (k : ℕ₋₂) (A : Type) : is_trunc_fun k (@id A) :=
λa, is_trunc_of_is_contr _ _ !is_contr_fiber_id

definition is_trunc_fun_compose (k : ℕ₋₂) {A B C : Type} {g : B → C} {f : A → B}
  (Hg : is_trunc_fun k g) (Hf : is_trunc_fun k f) : is_trunc_fun k (g ∘ f) :=
λc, is_trunc_equiv_closed_rev k (fiber_compose_equiv g f c) _
