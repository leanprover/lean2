/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Theorems about 2-dimensional paths
-/

import .cubical.square .function
open function is_equiv equiv sigma trunc

namespace eq
  variables {A B C : Type} {f : A → B} {a a' a₁ a₂ a₃ a₄ : A} {b b' : B}

  theorem ap_is_constant_eq (p : Πx, f x = b) (q : a = a') :
      ap_is_constant p q =
      eq_con_inv_of_con_eq ((eq_of_square (square_of_pathover (apd p q)))⁻¹ ⬝
      whisker_left (p a) (ap_constant q b)) :=
  begin
    induction q, esimp, generalize (p a), intro p, cases p, apply idpath idp
  end

  definition ap_inv2 {p q : a = a'} (r : p = q)
    : square (ap (ap f) (inverse2 r))
             (inverse2 (ap (ap f) r))
             (ap_inv f p)
             (ap_inv f q) :=
  by induction r;exact hrfl

  definition ap_con2 {p₁ q₁ : a₁ = a₂} {p₂ q₂ : a₂ = a₃} (r₁ : p₁ = q₁) (r₂ : p₂ = q₂)
    : square (ap (ap f) (r₁ ◾ r₂))
             (ap (ap f) r₁ ◾ ap (ap f) r₂)
             (ap_con f p₁ p₂)
             (ap_con f q₁ q₂) :=
  by induction r₂;induction r₁;exact hrfl

  theorem ap_con_right_inv_sq {A B : Type} {a1 a2 : A} (f : A → B) (p : a1 = a2) :
    square (ap (ap f) (con.right_inv p))
           (con.right_inv (ap f p))
           (ap_con f p p⁻¹ ⬝ whisker_left _ (ap_inv f p))
           idp :=
  by cases p;apply hrefl

  theorem ap_con_left_inv_sq {A B : Type} {a1 a2 : A} (f : A → B) (p : a1 = a2) :
    square (ap (ap f) (con.left_inv p))
           (con.left_inv (ap f p))
           (ap_con f p⁻¹ p ⬝ whisker_right _ (ap_inv f p))
           idp :=
  by cases p;apply vrefl

  definition ap02_compose {A B C : Type} (g : B → C) (f : A → B) {a a' : A}
    {p₁ p₂ : a = a'} (q : p₁ = p₂) :
    square (ap_compose g f p₁) (ap_compose g f p₂) (ap02 (g ∘ f) q) (ap02 g (ap02 f q)) :=
  by induction q; exact vrfl

  definition ap02_id {A : Type} {a a' : A}
    {p₁ p₂ : a = a'} (q : p₁ = p₂) :
    square (ap_id p₁) (ap_id p₂) (ap02 id q) q :=
  by induction q; exact vrfl

  theorem ap_ap_is_constant {A B C : Type} (g : B → C) {f : A → B} {b : B}
    (p : Πx, f x = b) {x y : A} (q : x = y) :
    square (ap (ap g) (ap_is_constant p q))
           (ap_is_constant (λa, ap g (p a)) q)
           (ap_compose g f q)⁻¹
           (!ap_con ⬝ whisker_left _ !ap_inv) :=
  begin
    induction q, esimp, generalize (p x), intro p, cases p, apply ids
--    induction q, rewrite [↑ap_compose,ap_inv], apply hinverse, apply ap_con_right_inv_sq,
  end

  theorem ap_ap_compose {A B C D : Type} (h : C → D) (g : B → C) (f : A → B)
    {x y : A} (p : x = y) :
    square (ap_compose (h ∘ g) f p)
           (ap (ap h) (ap_compose g f p))
           (ap_compose h (g ∘ f) p)
           (ap_compose h g (ap f p)) :=
  by induction p;exact ids

  theorem ap_compose_inv {A B C : Type} (g : B → C) (f : A → B)
    {x y : A} (p : x = y) :
    square (ap_compose g f p⁻¹)
           (inverse2 (ap_compose g f p) ⬝ (ap_inv g (ap f p))⁻¹)
           (ap_inv (g ∘ f) p)
           (ap (ap g) (ap_inv f p)) :=
  by induction p;exact ids

  theorem ap_compose_con (g : B → C) (f : A → B) (p : a₁ = a₂) (q : a₂ = a₃) :
    square (ap_compose g f (p ⬝ q))
           (ap_compose g f p ◾ ap_compose g f q ⬝ (ap_con g (ap f p) (ap f q))⁻¹)
           (ap_con (g ∘ f) p q)
           (ap (ap g) (ap_con f p q)) :=
  by induction q;induction p;exact ids

  theorem ap_compose_natural {A B C : Type} (g : B → C) (f : A → B)
    {x y : A} {p q : x = y} (r : p = q) :
    square (ap (ap (g ∘ f)) r)
           (ap (ap g ∘ ap f) r)
           (ap_compose g f p)
           (ap_compose g f q) :=
  natural_square_tr (ap_compose g f) r

  theorem whisker_right_eq_of_con_inv_eq_idp {p q : a₁ = a₂} (r : p ⬝ q⁻¹ = idp) :
    whisker_right q⁻¹ (eq_of_con_inv_eq_idp r) ⬝ con.right_inv q = r :=
  by induction q; esimp at r; cases r; reflexivity

  theorem ap_eq_of_con_inv_eq_idp (f : A → B) {p q : a₁ = a₂} (r : p ⬝ q⁻¹ = idp)
  : ap02 f (eq_of_con_inv_eq_idp r) =
           eq_of_con_inv_eq_idp (whisker_left _ !ap_inv⁻¹ ⬝ !ap_con⁻¹ ⬝ ap02 f r)
            :=
  by induction q;esimp at *;cases r;reflexivity

  theorem eq_of_con_inv_eq_idp_con2 {p p' q q' : a₁ = a₂} (r : p = p') (s : q = q')
    (t : p' ⬝ q'⁻¹ = idp)
  : eq_of_con_inv_eq_idp (r ◾ inverse2 s ⬝ t) = r ⬝ eq_of_con_inv_eq_idp t ⬝ s⁻¹ :=
  by induction s;induction r;induction q;reflexivity

  definition naturality_apd_eq {A : Type} {B : A → Type} {a a₂ : A} {f g : Πa, B a}
    (H : f ~ g) (p : a = a₂)
    : apd f p = concato_eq (eq_concato (H a) (apd g p)) (H a₂)⁻¹ :=
  begin
    induction p, esimp,
    generalizes [H a, g a], intro ga Ha, induction Ha,
    reflexivity
  end

  theorem con_tr_idp {P : A → Type} {x y : A} (q : x = y) (u : P x) :
    con_tr idp q u = ap (λp, p ▸ u) (idp_con q) :=
  by induction q;reflexivity

  definition eq_transport_Fl_idp_left {A B : Type} {a : A} {b : B} (f : A → B) (q : f a = b)
    : eq_transport_Fl idp q = !idp_con⁻¹ :=
  by induction q; reflexivity

  definition whisker_left_idp_con_eq_assoc
    {A : Type} {a₁ a₂ a₃ : A} (p : a₁ = a₂) (q : a₂ = a₃)
    : whisker_left p (idp_con q)⁻¹ = con.assoc p idp q :=
  by induction q; reflexivity

  definition whisker_left_inverse2 {A : Type} {a : A} {p : a = a} (q : p = idp)
    : whisker_left p q⁻² ⬝ q = con.right_inv p :=
  by cases q; reflexivity

  definition whisker_left_idp_square {A : Type} {a a' : A} {p q : a = a'} (r : p = q) :
    square (whisker_left idp r) r (idp_con p) (idp_con q) :=
  begin induction r, exact hrfl end

  definition cast_fn_cast_square {A : Type} {B C : A → Type} (f : Π⦃a⦄, B a → C a) {a₁ a₂ : A}
    (p : a₁ = a₂) (q : a₂ = a₁) (r : p ⬝ q = idp) (b : B a₁) :
    cast (ap C q) (f (cast (ap B p) b)) = f b :=
  have q⁻¹ = p, from inv_eq_of_idp_eq_con r⁻¹,
  begin induction this, induction q, reflexivity end

  definition ap011_ap_square_right {A B C : Type} (f : A → B → C) {a a' : A} (p : a = a')
    {b₁ b₂ b₃ : B} {q₁₂ : b₁ = b₂} {q₂₃ : b₂ = b₃} {q₁₃ : b₁ = b₃} (r : q₁₂ ⬝ q₂₃ = q₁₃) :
    square (ap011 f p q₁₂) (ap (λx, f x b₃) p) (ap (f a) q₁₃) (ap (f a') q₂₃) :=
  by induction r; induction q₂₃; induction q₁₂; induction p; exact ids

  definition ap011_ap_square_left {A B C : Type} (f : B → A → C) {a a' : A} (p : a = a')
    {b₁ b₂ b₃ : B} {q₁₂ : b₁ = b₂} {q₂₃ : b₂ = b₃} {q₁₃ : b₁ = b₃} (r : q₁₂ ⬝ q₂₃ = q₁₃) :
    square (ap011 f q₁₂ p) (ap (f b₃) p) (ap (λx, f x a) q₁₃) (ap (λx, f x a') q₂₃) :=
  by induction r; induction q₂₃; induction q₁₂; induction p; exact ids

  definition con2_assoc {A : Type} {x y z t : A} {p p' : x = y} {q q' : y = z} {r r' : z = t}
    (h : p = p') (h' : q = q') (h'' : r = r') :
    square ((h ◾ h') ◾ h'') (h ◾ (h' ◾ h'')) (con.assoc p q r) (con.assoc p' q' r') :=
  by induction h; induction h'; induction h''; exact hrfl

  definition con_left_inv_idp {A : Type} {x : A} {p : x = x} (q : p = idp)
    : con.left_inv p = q⁻² ◾ q :=
  by cases q; reflexivity

  definition eckmann_hilton_con2 {A : Type} {x : A} {p p' q q': idp = idp :> x = x}
    (h : p = p') (h' : q = q') : square (h ◾ h') (h' ◾ h) (eckmann_hilton p q) (eckmann_hilton p' q') :=
  by induction h; induction h'; exact hrfl

  definition ap_con_fn {A B : Type} {a a' : A} {b : B} (g h : A → b = b) (p : a = a') :
    ap (λa, g a ⬝ h a) p = ap g p ◾ ap h p :=
  by induction p; reflexivity

  definition ap_eq_ap011 {A B C X : Type} (f : A → B → C) (g : X → A) (h : X → B) {x x' : X}
    (p : x = x') : ap (λx, f (g x) (h x)) p = ap011 f (ap g p) (ap h p) :=
  by induction p; reflexivity

  definition ap_is_weakly_constant {A B : Type} {f : A → B}
    (h : is_weakly_constant f) {a a' : A} (p : a = a') : ap f p = (h a a)⁻¹ ⬝ h a a' :=
  by induction p; exact !con.left_inv⁻¹

  definition ap_is_constant_idp {A B : Type} {f : A → B} {b : B} (p : Πa, f a = b) {a : A} (q : a = a)
    (r : q = idp) : ap_is_constant p q = ap02 f r ⬝ (con.right_inv (p a))⁻¹ :=
  by cases r; exact !idp_con⁻¹

  definition con_right_inv_natural {A : Type} {a a' : A} {p p' : a = a'} (q : p = p') :
    con.right_inv p = q ◾ q⁻² ⬝ con.right_inv p' :=
  by induction q; induction p; reflexivity

  definition whisker_right_ap {A B : Type} {a a' : A}{b₁ b₂ b₃ : B} (q : b₂ = b₃) (f : A → b₁ = b₂)
    (p : a = a') : whisker_right q (ap f p) = ap (λa, f a ⬝ q) p :=
  by induction p; reflexivity

  definition ap02_ap_constant {A B C : Type} {a a' : A} (f : B → C) (b : B) (p : a = a') :
    square (ap_constant p (f b)) (ap02 f (ap_constant p b)) (ap_compose f (λx, b) p) idp :=
  by induction p; exact ids

  definition ap_constant_compose {A B C : Type} {a a' : A} (c : C) (f : A → B) (p : a = a') :
    square (ap_constant p c) (ap_constant (ap f p) c) (ap_compose (λx, c) f p) idp :=
  by induction p; exact ids

  definition ap02_constant {A B : Type} {a a' : A} (b : B) {p p' : a = a'}
    (q : p = p') : square (ap_constant p b) (ap_constant p' b) (ap02 (λx, b) q) idp :=
  by induction q; exact vrfl

  definition ap_con_idp_left {A B : Type} (f : A → B) {a a' : A} (p : a = a') :
    square (ap_con f idp p) idp (ap02 f (idp_con p)) (idp_con (ap f p)) :=
  begin induction p, exact ids end

  definition apd10_prepostcompose_nondep {A B C D : Type} (h : C → D) {g g' : B → C} (p : g = g')
    (f : A → B) (a : A) : apd10 (ap (λg a, h (g (f a))) p) a = ap h (apd10 p (f a)) :=
  begin induction p, reflexivity end

  definition apd10_prepostcompose {A B : Type} {C : B → Type} {D : A → Type}
    (f : A → B) (h : Πa, C (f a) → D a) {g g' : Πb, C b}
    (p : g = g') (a : A) :
    apd10 (ap (λg a, h a (g (f a))) p) a = ap (h a) (apd10 p (f a)) :=
  begin induction p, reflexivity end

  /- alternative induction principles -/
  definition eq.rec_to {A : Type} {a₀ : A} {P : Π⦃a₁⦄, a₀ = a₁ → Type}
    {a₁ : A} (p₀ : a₀ = a₁) (H : P p₀) ⦃a₂ : A⦄ (p : a₀ = a₂) : P p :=
  begin
    induction p₀, induction p, exact H
  end

  definition eq.rec_to2 {A : Type} {P : Π⦃a₀ a₁⦄, a₀ = a₁ → Type}
    {a₀ a₀' a₁' : A} (p' : a₀' = a₁') (p₀ : a₀ = a₀') (H : P p') ⦃a₁ : A⦄ (p : a₀ = a₁) : P p :=
  begin
   induction p₀, induction p', induction p, exact H
  end

  definition eq.rec_right_inv {A : Type} (f : A ≃ A) {P : Π⦃a₀ a₁⦄, f a₀ = a₁ → Type}
    (H : Πa, P (right_inv f a)) ⦃a₀ a₁ : A⦄ (p : f a₀ = a₁) : P p :=
  begin
    revert a₀ p, refine equiv_rect f⁻¹ᵉ _ _,
    intro a₀ p, exact eq.rec_to (right_inv f a₀) (H a₀) p,
  end

  definition eq.rec_equiv {A B : Type} {a₀ : A} (f : A ≃ B) {P : Π{a₁}, f a₀ = f a₁ → Type}
    (H : P (idpath (f a₀))) ⦃a₁ : A⦄ (p : f a₀ = f a₁) : P p :=
  begin
    assert qr : Σ(q : a₀ = a₁), ap f q = p,
    { exact ⟨eq_of_fn_eq_fn f p, ap_eq_of_fn_eq_fn' f p⟩ },
    cases qr with q r, apply transport P r, induction q, exact H
  end

  definition eq.rec_equiv_symm {A B : Type} {a₁ : A} (f : A ≃ B) {P : Π{a₀}, f a₀ = f a₁ → Type}
    (H : P (idpath (f a₁))) ⦃a₀ : A⦄ (p : f a₀ = f a₁) : P p :=
  begin
    assert qr : Σ(q : a₀ = a₁), ap f q = p,
    { exact ⟨eq_of_fn_eq_fn f p, ap_eq_of_fn_eq_fn' f p⟩ },
    cases qr with q r, apply transport P r, induction q, exact H
  end

  definition eq.rec_equiv_to_same {A B : Type} {a₀ : A} (f : A ≃ B) {P : Π{a₁}, f a₀ = f a₁ → Type}
    ⦃a₁' : A⦄ (p' : f a₀ = f a₁') (H : P p') ⦃a₁ : A⦄ (p : f a₀ = f a₁) : P p :=
  begin
    revert a₁' p' H a₁ p,
    refine eq.rec_equiv f _,
    exact eq.rec_equiv f
  end

  definition eq.rec_equiv_to {A A' B : Type} {a₀ : A} (f : A ≃ B) (g : A' ≃ B)
    {P : Π{a₁}, f a₀ = g a₁ → Type}
    ⦃a₁' : A'⦄ (p' : f a₀ = g a₁') (H : P p') ⦃a₁ : A'⦄ (p : f a₀ = g a₁) : P p :=
  begin
    assert qr : Σ(q : g⁻¹ (f a₀) = a₁), (right_inv g (f a₀))⁻¹ ⬝ ap g q = p,
    { exact ⟨eq_of_fn_eq_fn g (right_inv g (f a₀) ⬝ p),
             whisker_left _ (ap_eq_of_fn_eq_fn' g _) ⬝ !inv_con_cancel_left⟩ },
    assert q'r' : Σ(q' : g⁻¹ (f a₀) = a₁'), (right_inv g (f a₀))⁻¹ ⬝ ap g q' = p',
    { exact ⟨eq_of_fn_eq_fn g (right_inv g (f a₀) ⬝ p'),
             whisker_left _ (ap_eq_of_fn_eq_fn' g _) ⬝ !inv_con_cancel_left⟩ },
    induction qr with q r, induction q'r' with q' r',
    induction q, induction q',
    induction r, induction r',
    exact H
  end

  definition eq.rec_grading {A A' B : Type} {a : A} (f : A ≃ B) (g : A' ≃ B)
    {P : Π{b}, f a = b → Type}
    {a' : A'} (p' : f a = g a') (H : P p') ⦃b : B⦄ (p : f a = b) : P p :=
  begin
    revert b p, refine equiv_rect g _ _,
    exact eq.rec_equiv_to f g p' H
  end

  definition eq.rec_grading_unbased {A B B' C : Type} (f : A ≃ B) (g : B ≃ C) (h : B' ≃ C)
    {P : Π{b c}, g b = c → Type}
    {a' : A} {b' : B'} (p' : g (f a') = h b') (H : P p') ⦃b : B⦄ ⦃c : C⦄ (q : f a' = b)
    (p : g b = c) : P p :=
  begin
    induction q, exact eq.rec_grading (f ⬝e g) h p' H p
  end

end eq
