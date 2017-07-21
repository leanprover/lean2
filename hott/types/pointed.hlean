/-
Copyright (c) 2014-2016 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Floris van Doorn

Early library ported from Coq HoTT, but greatly extended since.
The basic definitions are in init.pointed

See also .pointed2
-/

import .nat.basic ..arity ..prop_trunc
open is_trunc eq prod sigma nat equiv option is_equiv bool unit sigma.ops sum algebra function

namespace pointed
  variables {A B : Type}

  definition pointed_loop [instance] [constructor] (a : A) : pointed (a = a) :=
  pointed.mk idp

  definition pointed_fun_closed [constructor] (f : A → B) [H : pointed A] : pointed B :=
  pointed.mk (f pt)

  definition loop [reducible] [constructor] (A : Type*) : Type* :=
  pointed.mk' (point A = point A)

  definition loopn [reducible] : ℕ → Type* → Type*
  | loopn  0    X := X
  | loopn (n+1) X := loop (loopn n X)

  notation `Ω` := loop
  notation `Ω[`:95 n:0 `]`:0 := loopn n

  namespace ops
    -- this is in a separate namespace because it caused type class inference to loop in some places
    definition is_trunc_pointed_MK [instance] [priority 1100] (n : ℕ₋₂) {A : Type} (a : A)
      [H : is_trunc n A] : is_trunc n (pointed.MK A a) :=
    H
  end ops

  definition is_trunc_loop [instance] [priority 1100] (A : Type*)
    (n : ℕ₋₂) [H : is_trunc (n.+1) A] : is_trunc n (Ω A) :=
  !is_trunc_eq

  definition loopn_zero_eq [unfold_full] (A : Type*)
    : Ω[0] A = A := rfl

  definition loopn_succ_eq [unfold_full] (k : ℕ) (A : Type*)
    : Ω[succ k] A = Ω (Ω[k] A) := rfl

  definition rfln  [constructor] [reducible] {n : ℕ} {A : Type*} : Ω[n] A := pt
  definition refln [constructor] [reducible] (n : ℕ) (A : Type*) : Ω[n] A := pt
  definition refln_eq_refl [unfold_full] (A : Type*) (n : ℕ) : rfln = rfl :> Ω[succ n] A := rfl

  definition loopn_space [unfold 3] (A : Type) [H : pointed A] (n : ℕ) : Type :=
  Ω[n] (pointed.mk' A)

  definition loop_mul {k : ℕ} {A : Type*} (mul : A → A → A) : Ω[k] A → Ω[k] A → Ω[k] A :=
  begin cases k with k, exact mul, exact concat end

  definition pType_eq {A B : Type*} (f : A ≃ B) (p : f pt = pt) : A = B :=
  begin
    cases A with A a, cases B with B b, esimp at *,
    fapply apdt011 @pType.mk,
    { apply ua f},
    { rewrite [cast_ua, p]},
  end

  definition pType_eq_elim {A B : Type*} (p : A = B :> Type*)
    : Σ(p : carrier A = carrier B :> Type), Point A =[p] Point B :=
  by induction p; exact ⟨idp, idpo⟩

  protected definition pType.sigma_char.{u} : pType.{u} ≃ Σ(X : Type.{u}), X :=
  begin
    fapply equiv.MK,
    { intro x, induction x with X x, exact ⟨X, x⟩},
    { intro x, induction x with X x, exact pointed.MK X x},
    { intro x, induction x with X x, reflexivity},
    { intro x, induction x with X x, reflexivity},
  end

  definition pType.eta_expand [constructor] (A : Type*) : Type* :=
  pointed.MK A pt

  definition add_point [constructor] (A : Type) : Type* :=
  pointed.Mk (none : option A)
  postfix `₊`:(max+1) := add_point
  -- the inclusion A → A₊ is called "some", the extra point "pt" or "none" ("@none A")
end pointed

namespace pointed
  /- truncated pointed types -/
  definition ptrunctype_eq {n : ℕ₋₂} {A B : n-Type*}
    (p : A = B :> Type) (q : Point A =[p] Point B) : A = B :=
  begin
    induction A with A HA a, induction B with B HB b, esimp at *,
    induction q, esimp,
    refine ap010 (ptrunctype.mk A) _ a,
    exact !is_prop.elim
  end

  definition ptrunctype_eq_of_pType_eq {n : ℕ₋₂} {A B : n-Type*} (p : A = B :> Type*)
    : A = B :=
  begin
    cases pType_eq_elim p with q r,
    exact ptrunctype_eq q r
  end

  definition is_trunc_ptrunctype [instance] {n : ℕ₋₂} (A : n-Type*) : is_trunc n A :=
  trunctype.struct A

end pointed open pointed

namespace pointed
  variables {A B C D : Type*} {f g h : A →* B} {P : A → Type} {p₀ : P pt} {k k' l m : ppi P p₀}

  /- categorical properties of pointed maps -/

  definition pid [constructor] (A : Type*) : A →* A :=
  pmap.mk id idp

  definition pcompose [constructor] {A B C : Type*} (g : B →* C) (f : A →* B) : A →* C :=
  pmap.mk (λa, g (f a)) (ap g (respect_pt f) ⬝ respect_pt g)

  infixr ` ∘* `:60 := pcompose

  definition pmap_of_map [constructor] {A B : Type} (f : A → B) (a : A) :
    pointed.MK A a →* pointed.MK B (f a) :=
  pmap.mk f idp

  definition respect_pt_pcompose {A B C : Type*} (g : B →* C) (f : A →* B)
    : respect_pt (g ∘* f) = ap g (respect_pt f) ⬝ respect_pt g :=
  idp

  definition passoc [constructor] (h : C →* D) (g : B →* C) (f : A →* B) : (h ∘* g) ∘* f ~* h ∘* (g ∘* f) :=
  phomotopy.mk (λa, idp)
    abstract !idp_con ⬝ whisker_right _ (!ap_con ⬝ whisker_right _ !ap_compose'⁻¹) ⬝ !con.assoc end

  definition pid_pcompose [constructor] (f : A →* B) : pid B ∘* f ~* f :=
  begin
    fapply phomotopy.mk,
    { intro a, reflexivity},
    { reflexivity}
  end

  definition pcompose_pid [constructor] (f : A →* B) : f ∘* pid A ~* f :=
  begin
    fapply phomotopy.mk,
    { intro a, reflexivity},
    { reflexivity}
  end

  /- equivalences and equalities -/

  protected definition ppi.sigma_char [constructor] {A : Type*} (B : A → Type) (b₀ : B pt) :
    ppi B b₀ ≃ Σ(k : Πa, B a), k pt = b₀ :=
  begin
    fapply equiv.MK: intro x,
    { constructor, exact respect_pt x },
    { induction x, constructor, assumption },
    { induction x, reflexivity },
    { induction x, reflexivity }
  end

  definition pmap.sigma_char [constructor] {A B : Type*} : (A →* B) ≃ Σ(f : A → B), f pt = pt :=
  !ppi.sigma_char

  definition pmap.eta_expand [constructor] {A B : Type*} (f : A →* B) : A →* B :=
  pmap.mk f (respect_pt f)

  definition pmap_equiv_right (A : Type*) (B : Type)
    : (Σ(b : B), A →* (pointed.Mk b)) ≃ (A → B) :=
  begin
    fapply equiv.MK,
    { intro u a, exact pmap.to_fun u.2 a},
    { intro f, refine ⟨f pt, _⟩, fapply pmap.mk,
        intro a, esimp, exact f a,
        reflexivity},
    { intro f, reflexivity},
    { intro u, cases u with b f, cases f with f p, esimp at *, induction p,
      reflexivity}
  end

  /- some specific pointed maps -/

  -- The constant pointed map between any two types
  definition pconst [constructor] (A B : Type*) : A →* B :=
  !ppi_const

  -- the pointed type of pointed maps -- TODO: remove
  definition ppmap [constructor] (A B : Type*) : Type* :=
  @pppi A (λa, B)

  definition pcast [constructor] {A B : Type*} (p : A = B) : A →* B :=
  pmap.mk (cast (ap pType.carrier p)) (by induction p; reflexivity)

  definition pinverse [constructor] {X : Type*} : Ω X →* Ω X :=
  pmap.mk eq.inverse idp

  /-
    we generalize the definition of ap1 to arbitrary paths, so that we can prove properties about it
    using path induction (see for example ap1_gen_con and ap1_gen_con_natural)
  -/
  definition ap1_gen [reducible] [unfold 6 9 10] {A B : Type} (f : A → B) {a a' : A}
    {b b' : B} (q : f a = b) (q' : f a' = b') (p : a = a') : b = b' :=
  q⁻¹ ⬝ ap f p ⬝ q'

  definition ap1_gen_idp [unfold 6] {A B : Type} (f : A → B) {a : A} {b : B} (q : f a = b) :
    ap1_gen f q q idp = idp :=
  con.left_inv q

  definition ap1_gen_idp_left [unfold 6] {A B : Type} (f : A → B) {a a' : A} (p : a = a') :
    ap1_gen f idp idp p = ap f p :=
  proof idp_con (ap f p) qed

  definition ap1_gen_idp_left_con {A B : Type} (f : A → B) {a : A} (p : a = a) (q : ap f p = idp) :
    ap1_gen_idp_left f p ⬝ q = proof ap (concat idp) q qed :=
  proof idp_con_idp q qed

  definition ap1 [constructor] (f : A →* B) : Ω A →* Ω B :=
  pmap.mk (λp, ap1_gen f (respect_pt f) (respect_pt f) p) (ap1_gen_idp f (respect_pt f))

  definition apn (n : ℕ) (f : A →* B) : Ω[n] A →* Ω[n] B :=
  begin
  induction n with n IH,
  { exact f},
  { esimp [loopn], exact ap1 IH}
  end

  notation `Ω→`:(max+5) := ap1
  notation `Ω→[`:95 n:0 `]`:0 := apn n

  definition ptransport [constructor] {A : Type} (B : A → Type*) {a a' : A} (p : a = a')
    : B a →* B a' :=
  pmap.mk (transport B p) (apdt (λa, Point (B a)) p)

  definition pmap_of_eq_pt [constructor] {A : Type} {a a' : A} (p : a = a') :
    pointed.MK A a →* pointed.MK A a' :=
  pmap.mk id p

  definition pbool_pmap [constructor] {A : Type*} (a : A) : pbool →* A :=
  pmap.mk (bool.rec pt a) idp

  /- properties of pointed maps -/

  definition apn_zero [unfold_full] (f : A →* B) : Ω→[0] f = f := idp
  definition apn_succ [unfold_full] (n : ℕ) (f : A →* B) : Ω→[n + 1] f = Ω→ (Ω→[n] f) := idp

  definition ap1_gen_con {A B : Type} (f : A → B) {a₁ a₂ a₃ : A} {b₁ b₂ b₃ : B}
    (q₁ : f a₁ = b₁) (q₂ : f a₂ = b₂) (q₃ : f a₃ = b₃) (p₁ : a₁ = a₂) (p₂ : a₂ = a₃) :
    ap1_gen f q₁ q₃ (p₁ ⬝ p₂) = ap1_gen f q₁ q₂ p₁ ⬝ ap1_gen f q₂ q₃ p₂ :=
  begin induction p₂, induction q₃, induction q₂, reflexivity end

  definition ap1_gen_inv {A B : Type} (f : A → B) {a₁ a₂ : A}
    {b₁ b₂ : B} (q₁ : f a₁ = b₁) (q₂ : f a₂ = b₂) (p₁ : a₁ = a₂) :
    ap1_gen f q₂ q₁ p₁⁻¹ = (ap1_gen f q₁ q₂ p₁)⁻¹ :=
  begin induction p₁, induction q₁, induction q₂, reflexivity end

  definition ap1_con {A B : Type*} (f : A →* B) (p q : Ω A) : ap1 f (p ⬝ q) = ap1 f p ⬝ ap1 f q :=
  ap1_gen_con f (respect_pt f) (respect_pt f) (respect_pt f) p q

  theorem ap1_inv (f : A →* B) (p : Ω A) : ap1 f p⁻¹ = (ap1 f p)⁻¹ :=
  ap1_gen_inv f (respect_pt f) (respect_pt f) p

  -- the following two facts are used for the suspension axiom to define spectrum cohomology
  definition ap1_gen_con_natural {A B : Type} (f : A → B) {a₁ a₂ a₃ : A} {p₁ p₁' : a₁ = a₂}
    {p₂ p₂' : a₂ = a₃}
    {b₁ b₂ b₃ : B} (q₁ : f a₁ = b₁) (q₂ : f a₂ = b₂) (q₃ : f a₃ = b₃)
    (r₁ : p₁ = p₁') (r₂ : p₂ = p₂') :
      square (ap1_gen_con f q₁ q₂ q₃ p₁ p₂)
             (ap1_gen_con f q₁ q₂ q₃ p₁' p₂')
             (ap (ap1_gen f q₁ q₃) (r₁ ◾ r₂))
             (ap (ap1_gen f q₁ q₂) r₁ ◾ ap (ap1_gen f q₂ q₃) r₂) :=
  begin induction r₁, induction r₂, exact vrfl end

  definition ap1_gen_con_idp {A B : Type} (f : A → B) {a : A} {b : B} (q : f a = b) :
    ap1_gen_con f q q q idp idp ⬝ con.left_inv q ◾ con.left_inv q = con.left_inv q :=
  by induction q; reflexivity

  definition apn_con (n : ℕ) (f : A →* B) (p q : Ω[n+1] A)
    : apn (n+1) f (p ⬝ q) = apn (n+1) f p ⬝ apn (n+1) f q :=
  ap1_con (apn n f) p q

  definition apn_inv (n : ℕ)  (f : A →* B) (p : Ω[n+1] A) : apn (n+1) f p⁻¹ = (apn (n+1) f p)⁻¹ :=
  ap1_inv (apn n f) p

  definition is_equiv_ap1 (f : A →* B) [is_equiv f] : is_equiv (ap1 f) :=
  begin
    induction B with B b, induction f with f pf, esimp at *, cases pf, esimp,
    apply is_equiv.homotopy_closed (ap f),
    intro p, exact !idp_con⁻¹
  end

  definition is_equiv_apn (n : ℕ) (f : A →* B) [H : is_equiv f]
    : is_equiv (apn n f) :=
  begin
    induction n with n IH,
    { exact H},
    { exact is_equiv_ap1 (apn n f)}
  end

  definition pinverse_con [constructor] {X : Type*} (p q : Ω X)
    : pinverse (p ⬝ q) = pinverse q ⬝ pinverse p :=
  !con_inv

  definition pinverse_inv [constructor] {X : Type*} (p : Ω X)
    : pinverse p⁻¹ = (pinverse p)⁻¹ :=
  idp

  definition ap1_pcompose_pinverse [constructor] {X Y : Type*} (f : X →* Y) :
    Ω→ f ∘* pinverse ~* pinverse ∘* Ω→ f :=
  phomotopy.mk (ap1_gen_inv f (respect_pt f) (respect_pt f))
    abstract begin
      induction Y with Y y₀, induction f with f f₀, esimp at * ⊢, induction f₀, reflexivity
    end end

  definition is_equiv_pcast [instance] {A B : Type*} (p : A = B) : is_equiv (pcast p) :=
  !is_equiv_cast

  /- categorical properties of pointed homotopies -/

  variable (k)
  protected definition phomotopy.refl [constructor] : k ~* k :=
  phomotopy.mk homotopy.rfl !idp_con
  variable {k}
  protected definition phomotopy.rfl [constructor] [refl] : k ~* k :=
  phomotopy.refl k

  protected definition phomotopy.symm [constructor] [symm] (p : k ~* l) : l ~* k :=
  phomotopy.mk p⁻¹ʰᵗʸ (inv_con_eq_of_eq_con (to_homotopy_pt p)⁻¹)

  protected definition phomotopy.trans [constructor] [trans] (p : k ~* l) (q : l ~* m) :
    k ~* m :=
  phomotopy.mk (λa, p a ⬝ q a) (!con.assoc ⬝ whisker_left (p pt) (to_homotopy_pt q) ⬝ to_homotopy_pt p)

  infix ` ⬝* `:75 := phomotopy.trans
  postfix `⁻¹*`:(max+1) := phomotopy.symm

  /- equalities and equivalences relating pointed homotopies -/

  definition phomotopy.rec' [recursor] (B : k ~* l → Type)
    (H : Π(h : k ~ l) (p : h pt ⬝ respect_pt l = respect_pt k), B (phomotopy.mk h p))
    (h : k ~* l) : B h :=
  begin
    induction h with h p,
    refine transport (λp, B (ppi.mk h p)) _ (H h (con_eq_of_eq_con_inv p)),
    apply to_left_inv !eq_con_inv_equiv_con_eq p
  end

  definition phomotopy.eta_expand [constructor] (p : k ~* l) : k ~* l :=
  phomotopy.mk p (to_homotopy_pt p)

  definition is_trunc_ppi [instance] (n : ℕ₋₂) {A : Type*} (B : A → Type) (b₀ : B pt) [Πa, is_trunc n (B a)] :
    is_trunc n (ppi B b₀) :=
  is_trunc_equiv_closed_rev _ !ppi.sigma_char

  definition is_trunc_pmap [instance] (n : ℕ₋₂) (A B : Type*) [is_trunc n B] :
    is_trunc n (A →* B) :=
  !is_trunc_ppi

  definition is_trunc_ppmap [instance] (n : ℕ₋₂) {A B : Type*} [is_trunc n B] :
    is_trunc n (ppmap A B) :=
  !is_trunc_pmap

  definition phomotopy_of_eq [constructor] (p : k = l) : k ~* l :=
  phomotopy.mk (ap010 ppi.to_fun p) begin induction p, refine !idp_con end

  definition phomotopy_of_eq_idp (k : ppi P p₀) : phomotopy_of_eq idp = phomotopy.refl k :=
  idp

  definition pconcat_eq [constructor] (p : k ~* l) (q : l = m) : k ~* m :=
  p ⬝* phomotopy_of_eq q

  definition eq_pconcat [constructor] (p : k = l) (q : l ~* m) : k ~* m :=
  phomotopy_of_eq p ⬝* q

  infix ` ⬝*p `:75 := pconcat_eq
  infix ` ⬝p* `:75 := eq_pconcat

  definition pr1_phomotopy_eq {p q : k ~* l} (r : p = q) (a : A) : p a = q a :=
  ap010 to_homotopy r a

  definition pwhisker_left [constructor] (h : B →* C) (p : f ~* g) : h ∘* f ~* h ∘* g :=
  phomotopy.mk (λa, ap h (p a))
    abstract !con.assoc⁻¹ ⬝ whisker_right _ (!ap_con⁻¹ ⬝ ap02 _ (to_homotopy_pt p)) end

  definition pwhisker_right [constructor] (h : C →* A) (p : f ~* g) : f ∘* h ~* g ∘* h :=
  phomotopy.mk (λa, p (h a))
    abstract !con.assoc⁻¹ ⬝ whisker_right _ (!ap_con_eq_con_ap)⁻¹ ⬝ !con.assoc ⬝
             whisker_left _ (to_homotopy_pt p) end

  definition pconcat2 [constructor] {A B C : Type*} {h i : B →* C} {f g : A →* B}
    (q : h ~* i) (p : f ~* g) : h ∘* f ~* i ∘* g :=
  pwhisker_left _ p ⬝* pwhisker_right _ q

  variables (k l)

  definition phomotopy.sigma_char [constructor]
    : (k ~* l) ≃ Σ(p : k ~ l), p pt ⬝ respect_pt l = respect_pt k :=
  begin
    fapply equiv.MK : intros h,
    { exact ⟨h , to_homotopy_pt h⟩ },
    { cases h with h p, exact phomotopy.mk h p },
    { cases h with h p, exact ap (dpair h) (to_right_inv !eq_con_inv_equiv_con_eq p) },
    { induction h using phomotopy.rec' with h p,
      exact ap (phomotopy.mk h) (to_right_inv !eq_con_inv_equiv_con_eq p) }
  end

  definition ppi_eq_equiv_internal : (k = l) ≃ (k ~* l) :=
    calc (k = l) ≃ ppi.sigma_char P p₀ k = ppi.sigma_char P p₀ l
                   : eq_equiv_fn_eq (ppi.sigma_char P p₀) k l
            ...  ≃ Σ(p : k = l),
                     pathover (λh, h pt = p₀) (respect_pt k) p (respect_pt l)
                   : sigma_eq_equiv _ _
            ...  ≃ Σ(p : k = l),
                     respect_pt k = ap (λh, h pt) p ⬝ respect_pt l
                   : sigma_equiv_sigma_right
                       (λp, eq_pathover_equiv_Fl p (respect_pt k) (respect_pt l))
            ...  ≃ Σ(p : k = l),
                     respect_pt k = apd10 p pt ⬝ respect_pt l
                   : sigma_equiv_sigma_right
                       (λp, equiv_eq_closed_right _ (whisker_right _ (ap_eq_apd10 p _)))
            ...  ≃ Σ(p : k ~ l), respect_pt k = p pt ⬝ respect_pt l
                   : sigma_equiv_sigma_left' eq_equiv_homotopy
            ...  ≃ Σ(p : k ~ l), p pt ⬝ respect_pt l = respect_pt k
                   : sigma_equiv_sigma_right (λp, eq_equiv_eq_symm _ _)
            ...  ≃ (k ~* l) : phomotopy.sigma_char k l

  definition ppi_eq_equiv_internal_idp :
    ppi_eq_equiv_internal k k idp = phomotopy.refl k :=
  begin
    apply ap (phomotopy.mk (homotopy.refl _)), induction k with k k₀,
    esimp at * ⊢, induction k₀, reflexivity
  end

  definition ppi_eq_equiv [constructor] : (k = l) ≃ (k ~* l) :=
  begin
    refine equiv_change_fun (ppi_eq_equiv_internal k l) _,
    { apply phomotopy_of_eq },
    { intro p, induction p, exact ppi_eq_equiv_internal_idp k }
  end
  variables {k l}

  definition pmap_eq_equiv [constructor] (f g : A →* B) : (f = g) ≃ (f ~* g) :=
  ppi_eq_equiv f g

  definition eq_of_phomotopy (p : k ~* l) : k = l :=
  to_inv (ppi_eq_equiv k l) p

  definition eq_of_phomotopy_refl {X Y : Type*} (f : X →* Y) :
    eq_of_phomotopy (phomotopy.refl f) = idpath f :=
  begin
    apply to_inv_eq_of_eq, reflexivity
  end

  definition phomotopy_of_homotopy (h : k ~ l) [Πa, is_set (P a)] : k ~* l :=
  begin
    fapply phomotopy.mk,
    { exact h },
    { apply is_set.elim }
  end

  definition ppi_eq_of_homotopy [Πa, is_set (P a)] (p : k ~ l) : k = l :=
  eq_of_phomotopy (phomotopy_of_homotopy p)

  definition pmap_eq_of_homotopy [is_set B] (p : f ~ g) : f = g :=
  ppi_eq_of_homotopy p

  definition phomotopy_of_eq_of_phomotopy (p : k ~* l) : phomotopy_of_eq (eq_of_phomotopy p) = p :=
  to_right_inv (ppi_eq_equiv k l) p

  definition phomotopy_rec_eq [recursor] {Q : (k ~* k') → Type} (p : k ~* k')
    (H : Π(q : k = k'), Q (phomotopy_of_eq q)) : Q p :=
  phomotopy_of_eq_of_phomotopy p ▸ H (eq_of_phomotopy p)

  definition phomotopy_rec_idp [recursor] {Q : Π {k' : ppi P p₀}, (k ~* k') → Type}
    {k' : ppi P p₀} (H : k ~* k') (q : Q (phomotopy.refl k)) : Q H :=
  begin
    induction H using phomotopy_rec_eq with t,
    induction t, exact phomotopy_of_eq_idp k ▸ q,
  end

  attribute phomotopy.rec' [recursor]

  definition phomotopy_rec_eq_phomotopy_of_eq {A B : Type*} {f g: A →* B}
    {Q : (f ~* g) → Type} (p : f = g) (H : Π(q : f = g), Q (phomotopy_of_eq q)) :
    phomotopy_rec_eq (phomotopy_of_eq p) H = H p :=
  begin
    unfold phomotopy_rec_eq,
    refine ap (λp, p ▸ _) !adj ⬝ _,
    refine !tr_compose⁻¹ ⬝ _,
    apply apdt
  end

  definition phomotopy_rec_idp_refl {A B : Type*} (f : A →* B)
    {Q : Π{g}, (f ~* g) → Type} (H : Q (phomotopy.refl f)) :
    phomotopy_rec_idp phomotopy.rfl H = H :=
  !phomotopy_rec_eq_phomotopy_of_eq

  /- adjunction between (-)₊ : Type → Type* and pType.carrier : Type* → Type  -/
  definition pmap_equiv_left (A : Type) (B : Type*) : A₊ →* B ≃ (A → B) :=
  begin
    fapply equiv.MK,
    { intro f a, cases f with f p, exact f (some a) },
    { intro f, fconstructor,
        intro a, cases a, exact pt, exact f a,
        reflexivity },
    { intro f, reflexivity },
    { intro f, cases f with f p, esimp, fapply eq_of_phomotopy, fapply phomotopy.mk,
      { intro a, cases a; all_goals (esimp at *), exact p⁻¹ },
      { esimp, exact !con.left_inv }},
  end

  -- pmap_pbool_pequiv is the pointed equivalence
  definition pmap_pbool_equiv [constructor] (B : Type*) : (pbool →* B) ≃ B :=
  begin
    fapply equiv.MK,
    { intro f, cases f with f p, exact f tt },
    { intro b, fconstructor,
        intro u, cases u, exact pt, exact b,
        reflexivity },
    { intro b, reflexivity },
    { intro f, cases f with f p, esimp, fapply eq_of_phomotopy, fapply phomotopy.mk,
      { intro a, cases a; all_goals (esimp at *), exact p⁻¹ },
      { esimp, exact !con.left_inv }},
  end

  /-
    Pointed maps respecting pointed homotopies.
    In general we need function extensionality for pap,
    but for particular F we can do it without function extensionality.
    This might be preferred, because such pointed homotopies compute. On the other hand,
    when using function extensionality, it's easier to prove that if p is reflexivity, then the
    resulting pointed homotopy is reflexivity
  -/
  definition pap (F : (A →* B) → (C →* D)) {f g : A →* B} (p : f ~* g) : F f ~* F g :=
  begin
    induction p using phomotopy_rec_idp, reflexivity
  end

  definition pap_refl (F : (A →* B) → (C →* D)) (f : A →* B) :
    pap F (phomotopy.refl f) = phomotopy.refl (F f) :=
  !phomotopy_rec_idp_refl

  definition ap1_phomotopy {f g : A →* B} (p : f ~* g) : Ω→ f ~* Ω→ g :=
  pap Ω→ p

  definition ap1_phomotopy_refl {X Y : Type*} (f : X →* Y) :
    ap1_phomotopy (phomotopy.refl f) = phomotopy.refl (Ω→ f) :=
  !pap_refl

  --a proof not using function extensionality:
  definition ap1_phomotopy_explicit {f g : A →* B} (p : f ~* g) : Ω→ f ~* Ω→ g :=
  begin
    induction p with p q, induction f with f pf, induction g with g pg, induction B with B b,
    esimp at * ⊢, induction q, induction pg,
    fapply phomotopy.mk,
    { intro l, refine _ ⬝ !idp_con⁻¹ᵖ, refine !con.assoc ⬝ _, apply inv_con_eq_of_eq_con,
      apply ap_con_eq_con_ap},
    { induction A with A a, unfold [ap_con_eq_con_ap], generalize p a, generalize g a, intro b q,
      induction q, reflexivity}
  end

  definition apn_phomotopy {f g : A →* B} (n : ℕ) (p : f ~* g) : apn n f ~* apn n g :=
  begin
    induction n with n IH,
    { exact p},
    { exact ap1_phomotopy IH}
  end

  -- the following two definitiongs are mostly the same, maybe we should remove one
  definition ap_eq_of_phomotopy {A B : Type*} {f g : A →* B} (p : f ~* g) (a : A) :
    ap (λf : A →* B, f a) (eq_of_phomotopy p) = p a :=
  ap010 to_homotopy (phomotopy_of_eq_of_phomotopy p) a

  definition to_fun_eq_of_phomotopy {A B : Type*} {f g : A →* B} (p : f ~* g) (a : A) :
    ap010 pmap.to_fun (eq_of_phomotopy p) a = p a :=
  begin
    induction p using phomotopy_rec_idp,
    exact ap (λx, ap010 pmap.to_fun x a) !eq_of_phomotopy_refl
  end

  definition ap1_eq_of_phomotopy {A B : Type*} {f g : A →* B} (p : f ~* g) :
    ap Ω→ (eq_of_phomotopy p) = eq_of_phomotopy (ap1_phomotopy p) :=
  begin
    induction p using phomotopy_rec_idp,
    refine ap02 _ !eq_of_phomotopy_refl ⬝ !eq_of_phomotopy_refl⁻¹ ⬝ ap eq_of_phomotopy _,
    exact !ap1_phomotopy_refl⁻¹
  end

  /- pointed homotopies between the given pointed maps -/

  definition ap1_pid [constructor] {A : Type*} : ap1 (pid A) ~* pid (Ω A) :=
  begin
    fapply phomotopy.mk,
    { intro p, esimp, refine !idp_con ⬝ !ap_id},
    { reflexivity}
  end

  definition ap1_pinverse [constructor] {A : Type*} : ap1 (@pinverse A) ~* @pinverse (Ω A) :=
  begin
    fapply phomotopy.mk,
    { intro p, refine !idp_con ⬝ _, exact !inv_eq_inv2⁻¹ },
    { reflexivity}
  end

  definition ap1_gen_compose {A B C : Type} (g : B → C) (f : A → B) {a₁ a₂ : A} {b₁ b₂ : B}
    {c₁ c₂ : C} (q₁ : f a₁ = b₁) (q₂ : f a₂ = b₂) (r₁ : g b₁ = c₁) (r₂ : g b₂ = c₂) (p : a₁ = a₂) :
    ap1_gen (g ∘ f) (ap g q₁ ⬝ r₁) (ap g q₂ ⬝ r₂) p = ap1_gen g r₁ r₂ (ap1_gen f q₁ q₂ p) :=
  begin induction p, induction q₁, induction q₂, induction r₁, induction r₂, reflexivity end

  definition ap1_gen_compose_idp {A B C : Type} (g : B → C) (f : A → B) {a : A}
    {b : B} {c : C} (q : f a = b) (r : g b = c) :
    ap1_gen_compose g f q q r r idp ⬝ (ap (ap1_gen g r r) (ap1_gen_idp f q) ⬝ ap1_gen_idp g r) =
    ap1_gen_idp (g ∘ f) (ap g q ⬝ r) :=
  begin induction q, induction r, reflexivity end

  definition ap1_pcompose [constructor] {A B C : Type*} (g : B →* C) (f : A →* B) :
    ap1 (g ∘* f) ~* ap1 g ∘* ap1 f :=
  phomotopy.mk (ap1_gen_compose g f (respect_pt f) (respect_pt f) (respect_pt g) (respect_pt g))
               (ap1_gen_compose_idp g f (respect_pt f) (respect_pt g))

  definition ap1_pconst [constructor] (A B : Type*) : Ω→(pconst A B) ~* pconst (Ω A) (Ω B) :=
  phomotopy.mk (λp, ap1_gen_idp_left (const A pt) p ⬝ ap_constant p pt) rfl

  definition ap1_gen_con_left {A B : Type} {a a' : A} {b₀ b₁ b₂ : B}
    {f : A → b₀ = b₁} {f' : A → b₁ = b₂} {q₀ q₁ : b₀ = b₁} {q₀' q₁' : b₁ = b₂}
    (r₀ : f a = q₀) (r₁ : f a' = q₁) (r₀' : f' a = q₀') (r₁' : f' a' = q₁') (p : a = a') :
      ap1_gen (λa, f a ⬝ f' a) (r₀ ◾ r₀') (r₁ ◾ r₁') p =
      whisker_right q₀' (ap1_gen f r₀ r₁ p) ⬝ whisker_left q₁ (ap1_gen f' r₀' r₁' p) :=
  begin induction r₀, induction r₁, induction r₀', induction r₁', induction p, reflexivity end

  definition ap1_gen_con_left_idp {A B : Type} {a : A} {b₀ b₁ b₂ : B}
    {f : A → b₀ = b₁} {f' : A → b₁ = b₂} {q₀ : b₀ = b₁} {q₁ : b₁ = b₂}
    (r₀ : f a = q₀) (r₁ : f' a = q₁) :
      ap1_gen_con_left r₀ r₀ r₁ r₁ idp =
      !con.left_inv ⬝ (ap (whisker_right q₁) !con.left_inv ◾ ap (whisker_left _) !con.left_inv)⁻¹ :=
  begin induction r₀, induction r₁, reflexivity end

  definition ptransport_change_eq [constructor] {A : Type} (B : A → Type*) {a a' : A} {p q : a = a'}
    (r : p = q) : ptransport B p ~* ptransport B q :=
  phomotopy.mk (λb, ap (λp, transport B p b) r) begin induction r, apply idp_con end

  definition pnatural_square {A B : Type} (X : B → Type*) {f g : A → B}
    (h : Πa, X (f a) →* X (g a)) {a a' : A} (p : a = a') :
    h a' ∘* ptransport X (ap f p) ~* ptransport X (ap g p) ∘* h a :=
  by induction p; exact !pcompose_pid ⬝* !pid_pcompose⁻¹*

  definition apn_pid [constructor] {A : Type*} (n : ℕ) : apn n (pid A) ~* pid (Ω[n] A) :=
  begin
    induction n with n IH,
    { reflexivity},
    { exact ap1_phomotopy IH ⬝* ap1_pid}
  end

  definition apn_pconst (A B : Type*) (n : ℕ) :
    apn n (pconst A B) ~* pconst (Ω[n] A) (Ω[n] B) :=
  begin
    induction n with n IH,
    { reflexivity },
    { exact ap1_phomotopy IH ⬝* !ap1_pconst }
  end

  definition apn_pcompose (n : ℕ) (g : B →* C) (f : A →* B) :
    apn n (g ∘* f) ~* apn n g ∘* apn n f :=
  begin
    induction n with n IH,
    { reflexivity},
    { refine ap1_phomotopy IH ⬝* _, apply ap1_pcompose}
  end

  definition pcast_idp [constructor] {A : Type*} : pcast (idpath A) ~* pid A :=
  by reflexivity

  definition pinverse_pinverse (A : Type*) : pinverse ∘* pinverse ~* pid (Ω A) :=
  begin
    fapply phomotopy.mk,
    { apply inv_inv},
    { reflexivity}
  end

  definition pcast_ap_loop [constructor] {A B : Type*} (p : A = B) :
    pcast (ap Ω p) ~* ap1 (pcast p) :=
  begin
    fapply phomotopy.mk,
    { intro a, induction p, esimp, exact (!idp_con ⬝ !ap_id)⁻¹},
    { induction p, reflexivity}
  end

  definition ap1_pmap_of_map [constructor] {A B : Type} (f : A → B) (a : A) :
    ap1 (pmap_of_map f a) ~* pmap_of_map (ap f) (idpath a) :=
  begin
    fapply phomotopy.mk,
    { intro a, esimp, apply idp_con},
    { reflexivity}
  end

  definition pcast_commute [constructor] {A : Type} {B C : A → Type*} (f : Πa, B a →* C a)
    {a₁ a₂ : A} (p : a₁ = a₂) : pcast (ap C p) ∘* f a₁ ~* f a₂ ∘* pcast (ap B p) :=
  phomotopy.mk
    begin induction p, reflexivity end
    begin induction p, esimp, refine !idp_con ⬝ !idp_con ⬝ !ap_id⁻¹ end

  /- pointed equivalences -/

  structure pequiv (A B : Type*) :=
  mk' :: (to_pmap : A →* B)
         (to_pinv1 : B →* A)
         (to_pinv2 : B →* A)
         (pright_inv : to_pmap ∘* to_pinv1 ~* pid B)
         (pleft_inv : to_pinv2 ∘* to_pmap ~* pid A)

  infix ` ≃* `:25 := pequiv

  definition pmap_of_pequiv [unfold 3] [coercion] [reducible] {A B : Type*} (f : A ≃* B) :
    @ppi A (λa, B) pt :=
  pequiv.to_pmap f

  definition to_pinv [unfold 3] (f : A ≃* B) : B →* A :=
  pequiv.to_pinv1 f

  definition pleft_inv' (f : A ≃* B) : to_pinv f ∘* f ~* pid A :=
  let g := to_pinv f in
  let h := pequiv.to_pinv2 f in
  calc g ∘* f ~* pid A ∘* (g ∘* f)    : by exact !pid_pcompose⁻¹*
          ... ~* (h ∘* f) ∘* (g ∘* f) : by exact pwhisker_right _ (pequiv.pleft_inv f)⁻¹*
          ... ~* h ∘* (f ∘* g) ∘* f   : by exact !passoc ⬝* pwhisker_left _ !passoc⁻¹*
          ... ~* h ∘* pid B ∘* f      : by exact !pwhisker_left (!pwhisker_right !pequiv.pright_inv)
          ... ~* h ∘* f               : by exact pwhisker_left _ !pid_pcompose
          ... ~* pid A                : by exact pequiv.pleft_inv f

  definition equiv_of_pequiv [coercion] [constructor] (f : A ≃* B) : A ≃ B :=
  have is_equiv f, from adjointify f (to_pinv f) (pequiv.pright_inv f) (pleft_inv' f),
  equiv.mk f _

  attribute pointed._trans_of_equiv_of_pequiv pointed._trans_of_pmap_of_pequiv [unfold 3]

  definition pequiv.to_is_equiv [instance] [constructor] (f : A ≃* B) :
    is_equiv (pointed._trans_of_equiv_of_pequiv f) :=
  adjointify f (to_pinv f) (pequiv.pright_inv f) (pleft_inv' f)

  definition pequiv.to_is_equiv' [instance] [constructor] (f : A ≃* B) :
    is_equiv (pointed._trans_of_pmap_of_pequiv f) :=
  pequiv.to_is_equiv f

  protected definition pequiv.MK [constructor] (f : A →* B) (g : B →* A)
    (gf : g ∘* f ~* !pid) (fg : f ∘* g ~* !pid) : A ≃* B :=
  pequiv.mk' f g g fg gf

  definition pinv [constructor] (f : A →* B) (H : is_equiv f) : B →* A :=
  pmap.mk f⁻¹ᶠ (ap f⁻¹ᶠ (respect_pt f)⁻¹ ⬝ (left_inv f pt))

  definition pequiv_of_pmap [constructor] (f : A →* B) (H : is_equiv f) : A ≃* B :=
  pequiv.mk' f (pinv f H) (pinv f H)
  abstract begin
    fapply phomotopy.mk, exact right_inv f,
    induction f with f f₀, induction B with B b₀, esimp at *, induction f₀, esimp,
    exact adj f pt ⬝ ap02 f !idp_con⁻¹
  end end
  abstract begin
    fapply phomotopy.mk, exact left_inv f,
    induction f with f f₀, induction B with B b₀, esimp at *, induction f₀, esimp,
    exact !idp_con⁻¹ ⬝ !idp_con⁻¹
  end end

  definition pequiv.mk [constructor] (f : A → B) (H : is_equiv f) (p : f pt = pt) : A ≃* B :=
  pequiv_of_pmap (pmap.mk f p) H

  definition pequiv_of_equiv [constructor] (f : A ≃ B) (H : f pt = pt) : A ≃* B :=
  pequiv.mk f _ H

  protected definition pequiv.MK' [constructor] (f : A →* B) (g : B → A)
    (gf : Πa, g (f a) = a) (fg : Πb, f (g b) = b) : A ≃* B :=
  pequiv.mk f (adjointify f g fg gf) (respect_pt f)

  /- reflexivity and symmetry (transitivity is below) -/

  protected definition pequiv.refl [refl] [constructor] (A : Type*) : A ≃* A :=
  pequiv.mk' (pid A) (pid A) (pid A) !pid_pcompose !pcompose_pid

  protected definition pequiv.rfl [constructor] : A ≃* A :=
  pequiv.refl A

  protected definition pequiv.symm [symm] [constructor] (f : A ≃* B) : B ≃* A :=
  pequiv.MK (to_pinv f) f (pequiv.pright_inv f) (pleft_inv' f)

  postfix `⁻¹ᵉ*`:(max + 1) := pequiv.symm

  definition pleft_inv (f : A ≃* B) : f⁻¹ᵉ* ∘* f ~* pid A :=
  pleft_inv' f

  definition pright_inv (f : A ≃* B) : f ∘* f⁻¹ᵉ* ~* pid B :=
  pequiv.pright_inv f

  definition to_pmap_pequiv_of_pmap {A B : Type*} (f : A →* B) (H : is_equiv f)
    : pequiv.to_pmap (pequiv_of_pmap f H) = f :=
  by reflexivity

  definition to_pmap_pequiv_MK [constructor] (f : A →* B) (g : B →* A)
    (gf : g ∘* f ~* !pid) (fg : f ∘* g ~* !pid) : pequiv.MK f g gf fg ~* f :=
  by reflexivity

  definition to_pinv_pequiv_MK [constructor] (f : A →* B) (g : B →* A)
    (gf : g ∘* f ~* !pid) (fg : f ∘* g ~* !pid) : to_pinv (pequiv.MK f g gf fg) ~* g :=
  by reflexivity

  /- more on pointed equivalences -/

  definition pequiv_ap [constructor] {A : Type} (B : A → Type*) {a a' : A} (p : a = a')
    : B a ≃* B a' :=
  pequiv_of_pmap (ptransport B p) !is_equiv_tr

  definition pequiv_change_fun [constructor] (f : A ≃* B) (f' : A →* B) (Heq : f ~ f') : A ≃* B :=
  pequiv_of_pmap f' (is_equiv.homotopy_closed f Heq)

  definition pequiv_change_inv [constructor] (f : A ≃* B) (f' : B →* A) (Heq : to_pinv f ~ f')
    : A ≃* B :=
  pequiv.MK' f f' (to_left_inv (equiv_change_inv f Heq)) (to_right_inv (equiv_change_inv f Heq))

  definition pequiv_rect' (f : A ≃* B) (P : A → B → Type)
    (g : Πb, P (f⁻¹ b) b) (a : A) : P a (f a) :=
  left_inv f a ▸ g (f a)

  definition pua {A B : Type*} (f : A ≃* B) : A = B :=
  pType_eq (equiv_of_pequiv f) !respect_pt

  definition pequiv_of_eq [constructor] {A B : Type*} (p : A = B) : A ≃* B :=
  pequiv_of_pmap (pcast p) !is_equiv_tr

  definition eq_of_pequiv {A B : Type*} (p : A ≃* B) : A = B :=
  pType_eq (equiv_of_pequiv p) !respect_pt

  definition peap {A B : Type*} (F : Type* → Type*) (p : A ≃* B) : F A ≃* F B :=
  pequiv_of_pmap (pcast (ap F (eq_of_pequiv p))) begin cases eq_of_pequiv p, apply is_equiv_id end

  -- rename pequiv_of_eq_natural
  definition pequiv_of_eq_commute [constructor] {A : Type} {B C : A → Type*} (f : Πa, B a →* C a)
    {a₁ a₂ : A} (p : a₁ = a₂) : pequiv_of_eq (ap C p) ∘* f a₁ ~* f a₂ ∘* pequiv_of_eq (ap B p) :=
  pcast_commute f p

  -- definition pequiv.eta_expand [constructor] {A B : Type*} (f : A ≃* B) : A ≃* B :=
  -- pequiv.mk' f (to_pinv f) (pequiv.to_pinv2 f) (pright_inv f) _

  /-
    the theorem pequiv_eq, which gives a condition for two pointed equivalences are equal
    is in types.equiv to avoid circular imports
  -/

  /- computation rules of pointed homotopies, possibly combined with pointed equivalences -/
  definition pcancel_left (f : B ≃* C) {g h : A →* B} (p : f ∘* g ~* f ∘* h) : g ~* h :=
  begin
    refine _⁻¹* ⬝* pwhisker_left f⁻¹ᵉ* p ⬝* _:
    refine !passoc⁻¹* ⬝* _:
    refine pwhisker_right _ (pleft_inv f) ⬝* _:
    apply pid_pcompose
  end

  definition pcancel_right (f : A ≃* B) {g h : B →* C} (p : g ∘* f ~* h ∘* f) : g ~* h :=
  begin
    refine _⁻¹* ⬝* pwhisker_right f⁻¹ᵉ* p ⬝* _:
    refine !passoc ⬝* _:
    refine pwhisker_left _ (pright_inv f) ⬝* _:
    apply pcompose_pid
  end

  definition phomotopy_pinv_right_of_phomotopy {f : A ≃* B} {g : B →* C} {h : A →* C}
    (p : g ∘* f ~* h) : g ~* h ∘* f⁻¹ᵉ* :=
  begin
    refine _ ⬝* pwhisker_right _ p, symmetry,
    refine !passoc ⬝* _,
    refine pwhisker_left _ (pright_inv f) ⬝* _,
    apply pcompose_pid
  end

  definition phomotopy_of_pinv_right_phomotopy {f : B ≃* A} {g : B →* C} {h : A →* C}
    (p : g ∘* f⁻¹ᵉ* ~* h) : g ~* h ∘* f :=
  begin
    refine _ ⬝* pwhisker_right _ p, symmetry,
    refine !passoc ⬝* _,
    refine pwhisker_left _ (pleft_inv f) ⬝* _,
    apply pcompose_pid
  end

  definition pinv_right_phomotopy_of_phomotopy {f : A ≃* B} {g : B →* C} {h : A →* C}
    (p : h ~* g ∘* f) : h ∘* f⁻¹ᵉ* ~* g :=
  (phomotopy_pinv_right_of_phomotopy p⁻¹*)⁻¹*

  definition phomotopy_of_phomotopy_pinv_right {f : B ≃* A} {g : B →* C} {h : A →* C}
    (p : h ~* g ∘* f⁻¹ᵉ*) : h ∘* f ~* g :=
  (phomotopy_of_pinv_right_phomotopy p⁻¹*)⁻¹*

  definition phomotopy_pinv_left_of_phomotopy {f : B ≃* C} {g : A →* B} {h : A →* C}
    (p : f ∘* g ~* h) : g ~* f⁻¹ᵉ* ∘* h :=
  begin
    refine _ ⬝* pwhisker_left _ p, symmetry,
    refine !passoc⁻¹* ⬝* _,
    refine pwhisker_right _ (pleft_inv f) ⬝* _,
    apply pid_pcompose
  end

  definition phomotopy_of_pinv_left_phomotopy {f : C ≃* B} {g : A →* B} {h : A →* C}
    (p : f⁻¹ᵉ* ∘* g ~* h) : g ~* f ∘* h :=
  begin
    refine _ ⬝* pwhisker_left _ p, symmetry,
    refine !passoc⁻¹* ⬝* _,
    refine pwhisker_right _ (pright_inv f) ⬝* _,
    apply pid_pcompose
  end

  definition pinv_left_phomotopy_of_phomotopy {f : B ≃* C} {g : A →* B} {h : A →* C}
    (p : h ~* f ∘* g) : f⁻¹ᵉ* ∘* h ~* g :=
  (phomotopy_pinv_left_of_phomotopy p⁻¹*)⁻¹*

  definition phomotopy_of_phomotopy_pinv_left {f : C ≃* B} {g : A →* B} {h : A →* C}
    (p : h ~* f⁻¹ᵉ* ∘* g) : f ∘* h ~* g :=
  (phomotopy_of_pinv_left_phomotopy p⁻¹*)⁻¹*

  definition pcompose2 {A B C : Type*} {g g' : B →* C} {f f' : A →* B} (q : g ~* g') (p : f ~* f') :
    g ∘* f ~* g' ∘* f' :=
  pwhisker_right f q ⬝* pwhisker_left g' p

  infixr ` ◾* `:80 := pcompose2

  definition phomotopy_pinv_of_phomotopy_pid {A B : Type*} {f : A →* B} {g : B ≃* A}
    (p : g ∘* f ~* pid A) : f ~* g⁻¹ᵉ* :=
  phomotopy_pinv_left_of_phomotopy p ⬝* !pcompose_pid

  definition phomotopy_pinv_of_phomotopy_pid' {A B : Type*} {f : A →* B} {g : B ≃* A}
    (p : f ∘* g ~* pid B) : f ~* g⁻¹ᵉ* :=
  phomotopy_pinv_right_of_phomotopy p ⬝* !pid_pcompose

  definition pinv_phomotopy_of_pid_phomotopy {A B : Type*} {f : A →* B} {g : B ≃* A}
    (p : pid A ~* g ∘* f) : g⁻¹ᵉ* ~* f :=
  (phomotopy_pinv_of_phomotopy_pid p⁻¹*)⁻¹*

  definition pinv_phomotopy_of_pid_phomotopy' {A B : Type*} {f : A →* B} {g : B ≃* A}
    (p : pid B ~* f ∘* g) : g⁻¹ᵉ* ~* f :=
  (phomotopy_pinv_of_phomotopy_pid' p⁻¹*)⁻¹*

  definition pinv_pcompose_cancel_left {A B C : Type*} (g : B ≃* C) (f : A →* B) :
    g⁻¹ᵉ* ∘* (g ∘* f) ~* f :=
  !passoc⁻¹* ⬝* pwhisker_right f !pleft_inv ⬝* !pid_pcompose

  definition pcompose_pinv_cancel_left {A B C : Type*} (g : C ≃* B) (f : A →* B) :
    g ∘* (g⁻¹ᵉ* ∘* f) ~* f :=
  !passoc⁻¹* ⬝* pwhisker_right f !pright_inv ⬝* !pid_pcompose

  definition pinv_pcompose_cancel_right {A B C : Type*} (g : B →* C) (f : B ≃* A) :
    (g ∘* f⁻¹ᵉ*) ∘* f ~* g :=
  !passoc ⬝* pwhisker_left g !pleft_inv ⬝* !pcompose_pid

  definition pcompose_pinv_cancel_right {A B C : Type*} (g : B →* C) (f : A ≃* B) :
    (g ∘* f) ∘* f⁻¹ᵉ* ~* g :=
  !passoc ⬝* pwhisker_left g !pright_inv ⬝* !pcompose_pid

  definition pinv_pinv {A B : Type*} (f : A ≃* B) : (f⁻¹ᵉ*)⁻¹ᵉ* ~* f :=
  (phomotopy_pinv_of_phomotopy_pid (pleft_inv f))⁻¹*

  definition pinv2 {A B : Type*} {f f' : A ≃* B} (p : f ~* f') : f⁻¹ᵉ* ~* f'⁻¹ᵉ* :=
  phomotopy_pinv_of_phomotopy_pid (pinv_right_phomotopy_of_phomotopy (!pid_pcompose ⬝* p)⁻¹*)

  postfix [parsing_only] `⁻²*`:(max+10) := pinv2

  protected definition pequiv.trans [trans] [constructor] (f : A ≃* B) (g : B ≃* C) : A ≃* C :=
  pequiv.MK (g ∘* f) (f⁻¹ᵉ* ∘* g⁻¹ᵉ*)
    abstract !passoc ⬝* pwhisker_left _ (pinv_pcompose_cancel_left g f) ⬝* pleft_inv f end
    abstract !passoc ⬝* pwhisker_left _ (pcompose_pinv_cancel_left f g⁻¹ᵉ*) ⬝* pright_inv g end

  definition pequiv_compose {A B C : Type*} (g : B ≃* C) (f : A ≃* B) : A ≃* C :=
  pequiv.trans f g

  infix ` ⬝e* `:75 := pequiv.trans
  infixr ` ∘*ᵉ `:60 := pequiv_compose

  definition to_pmap_pequiv_trans {A B C : Type*} (f : A ≃* B) (g : B ≃* C)
    : pequiv.to_pmap (f ⬝e* g) = g ∘* f :=
  by reflexivity

  definition to_fun_pequiv_trans {X Y Z : Type*} (f : X ≃* Y) (g :Y ≃* Z) : f ⬝e* g ~ g ∘ f :=
  λx, idp

  definition peconcat_eq {A B C : Type*} (p : A ≃* B) (q : B = C) : A ≃* C :=
  p ⬝e* pequiv_of_eq q

  definition eq_peconcat {A B C : Type*} (p : A = B) (q : B ≃* C) : A ≃* C :=
  pequiv_of_eq p ⬝e* q


  infix ` ⬝e*p `:75 := peconcat_eq
  infix ` ⬝pe* `:75 := eq_peconcat


  definition trans_pinv {A B C : Type*} (f : A ≃* B) (g : B ≃* C) :
    (f ⬝e* g)⁻¹ᵉ* ~* f⁻¹ᵉ* ∘* g⁻¹ᵉ* :=
  by reflexivity

  definition pinv_trans_pinv_left {A B C : Type*} (f : B ≃* A) (g : B ≃* C) :
    (f⁻¹ᵉ* ⬝e* g)⁻¹ᵉ* ~* f ∘* g⁻¹ᵉ* :=
  by reflexivity

  definition pinv_trans_pinv_right {A B C : Type*} (f : A ≃* B) (g : C ≃* B) :
    (f ⬝e* g⁻¹ᵉ*)⁻¹ᵉ* ~* f⁻¹ᵉ* ∘* g :=
  by reflexivity

  definition pinv_trans_pinv_pinv {A B C : Type*} (f : B ≃* A) (g : C ≃* B) :
    (f⁻¹ᵉ* ⬝e* g⁻¹ᵉ*)⁻¹ᵉ* ~* f ∘* g :=
  by reflexivity

  /- pointed equivalences between particular pointed types -/

  -- TODO: remove is_equiv_apn, which is proven again here
  definition loopn_pequiv_loopn [constructor] (n : ℕ) (f : A ≃* B) : Ω[n] A ≃* Ω[n] B :=
  pequiv.MK (apn n f) (apn n f⁻¹ᵉ*)
  abstract begin
    induction n with n IH,
    { apply pleft_inv},
    { replace nat.succ n with n + 1,
      rewrite [+apn_succ],
      refine !ap1_pcompose⁻¹* ⬝* _,
      refine ap1_phomotopy IH ⬝* _,
      apply ap1_pid}
  end end
  abstract begin
    induction n with n IH,
    { apply pright_inv},
    { replace nat.succ n with n + 1,
      rewrite [+apn_succ],
      refine !ap1_pcompose⁻¹* ⬝* _,
      refine ap1_phomotopy IH ⬝* _,
      apply ap1_pid}
  end end

  definition loop_pequiv_loop [constructor] (f : A ≃* B) : Ω A ≃* Ω B :=
  loopn_pequiv_loopn 1 f

  definition loop_pequiv_eq_closed [constructor] {A : Type} {a a' : A} (p : a = a')
    : pointed.MK (a = a) idp ≃* pointed.MK (a' = a') idp :=
  pequiv_of_equiv (loop_equiv_eq_closed p) (con.left_inv p)

  definition to_pmap_loopn_pequiv_loopn [constructor] (n : ℕ) (f : A ≃* B)
    : loopn_pequiv_loopn n f ~* apn n f :=
  by reflexivity

  definition to_pinv_loopn_pequiv_loopn [constructor] (n : ℕ) (f : A ≃* B)
    : (loopn_pequiv_loopn n f)⁻¹ᵉ* ~* apn n f⁻¹ᵉ* :=
  by reflexivity

  definition loopn_pequiv_loopn_con (n : ℕ) (f : A ≃* B) (p q : Ω[n+1] A)
    : loopn_pequiv_loopn (n+1) f (p ⬝ q) =
    loopn_pequiv_loopn (n+1) f p ⬝ loopn_pequiv_loopn (n+1) f q :=
  ap1_con (loopn_pequiv_loopn n f) p q

  definition loop_pequiv_loop_con {A B : Type*} (f : A ≃* B) (p q : Ω A)
    : loop_pequiv_loop f (p ⬝ q) = loop_pequiv_loop f p ⬝ loop_pequiv_loop f q :=
  loopn_pequiv_loopn_con 0 f p q

  definition loopn_pequiv_loopn_rfl (n : ℕ) (A : Type*) :
    loopn_pequiv_loopn n (pequiv.refl A) ~* pequiv.refl (Ω[n] A) :=
  begin
    exact !to_pmap_loopn_pequiv_loopn ⬝* apn_pid n,
  end

  definition loop_pequiv_loop_rfl (A : Type*) :
    loop_pequiv_loop (pequiv.refl A) ~* pequiv.refl (Ω A) :=
  loopn_pequiv_loopn_rfl 1 A

  definition apn_pinv (n : ℕ) {A B : Type*} (f : A ≃* B) :
    Ω→[n] f⁻¹ᵉ* ~* (loopn_pequiv_loopn n f)⁻¹ᵉ* :=
  by reflexivity

  definition pmap_functor [constructor] {A A' B B' : Type*} (f : A' →* A) (g : B →* B') :
    ppmap A B →* ppmap A' B' :=
  pmap.mk (λh, g ∘* h ∘* f)
    abstract begin
      fapply eq_of_phomotopy, fapply phomotopy.mk,
      { esimp, intro a, exact respect_pt g},
      { rewrite [▸*, ap_constant], exact !idp_con⁻¹ }
    end end

  definition pequiv_pinverse (A : Type*) : Ω A ≃* Ω A :=
  pequiv_of_pmap pinverse !is_equiv_eq_inverse

  definition pequiv_of_eq_pt [constructor] {A : Type} {a a' : A} (p : a = a') :
    pointed.MK A a ≃* pointed.MK A a' :=
  pequiv_of_pmap (pmap_of_eq_pt p) !is_equiv_id

  definition pointed_eta_pequiv [constructor] (A : Type*) : A ≃* pointed.MK A pt :=
  pequiv.mk id !is_equiv_id idp

  /- every pointed map is homotopic to one of the form `pmap_of_map _ _`, up to some
     pointed equivalences -/
  definition phomotopy_pmap_of_map {A B : Type*} (f : A →* B) :
    (pointed_eta_pequiv B ⬝e* (pequiv_of_eq_pt (respect_pt f))⁻¹ᵉ*) ∘* f ∘*
      (pointed_eta_pequiv A)⁻¹ᵉ* ~* pmap_of_map f pt :=
  begin
    fapply phomotopy.mk,
    { reflexivity},
    { symmetry, exact (!ap_id ⬝ !idp_con) ◾ (!idp_con ⬝ !ap_id) ⬝ !con.right_inv }
  end

  /- properties of iterated loop space -/
  variable (A)
  definition loopn_succ_in (n : ℕ) : Ω[succ n] A ≃* Ω[n] (Ω A) :=
  begin
    induction n with n IH,
    { reflexivity},
    { exact loop_pequiv_loop IH}
  end

  definition loopn_add (n m : ℕ) : Ω[n] (Ω[m] A) ≃* Ω[m+n] (A) :=
  begin
    induction n with n IH,
    { reflexivity},
    { exact loop_pequiv_loop IH}
  end

  definition loopn_succ_out (n : ℕ) : Ω[succ n] A ≃* Ω(Ω[n] A)  :=
  by reflexivity

  variable {A}

  definition loopn_succ_in_con {n : ℕ} (p q : Ω[succ (succ n)] A) :
    loopn_succ_in A (succ n) (p ⬝ q) =
    loopn_succ_in A (succ n) p ⬝ loopn_succ_in A (succ n) q :=
  !loop_pequiv_loop_con

  definition loopn_loop_irrel (p : point A = point A) : Ω(pointed.Mk p) = Ω[2] A :=
  begin
    intros, fapply pType_eq,
    { esimp, transitivity _,
      apply eq_equiv_fn_eq_of_equiv (equiv_eq_closed_right _ p⁻¹),
      esimp, apply eq_equiv_eq_closed, apply con.right_inv, apply con.right_inv},
    { esimp, apply con.left_inv}
  end

  definition loopn_space_loop_irrel (n : ℕ) (p : point A = point A)
    : Ω[succ n](pointed.Mk p) = Ω[succ (succ n)] A :> pType :=
  calc
    Ω[succ n](pointed.Mk p) = Ω[n](Ω (pointed.Mk p)) : eq_of_pequiv !loopn_succ_in
      ... = Ω[n] (Ω[2] A)                            : loopn_loop_irrel
      ... = Ω[2+n] A                                 : eq_of_pequiv !loopn_add
      ... = Ω[n+2] A                                 : by rewrite [algebra.add.comm]

  definition apn_succ_phomotopy_in (n : ℕ) (f : A →* B) :
    loopn_succ_in B n ∘* Ω→[n + 1] f ~* Ω→[n] (Ω→ f) ∘* loopn_succ_in A n :=
  begin
    induction n with n IH,
    { reflexivity},
    { exact !ap1_pcompose⁻¹* ⬝* ap1_phomotopy IH ⬝* !ap1_pcompose}
  end

  definition loopn_succ_in_natural {A B : Type*} (n : ℕ) (f : A →* B) :
    loopn_succ_in B n ∘* Ω→[n+1] f ~* Ω→[n] (Ω→ f) ∘* loopn_succ_in A n :=
  !apn_succ_phomotopy_in

  definition loopn_succ_in_inv_natural {A B : Type*} (n : ℕ) (f : A →* B) :
    Ω→[n + 1] f ∘* (loopn_succ_in A n)⁻¹ᵉ* ~* (loopn_succ_in B n)⁻¹ᵉ* ∘* Ω→[n] (Ω→ f):=
  begin
    apply pinv_right_phomotopy_of_phomotopy,
    refine _ ⬝* !passoc⁻¹*,
    apply phomotopy_pinv_left_of_phomotopy,
    apply apn_succ_phomotopy_in
  end

end pointed
