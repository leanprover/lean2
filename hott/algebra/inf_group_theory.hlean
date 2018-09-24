/-
Copyright (c) 2018 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/

import .bundled .homomorphism types.nat.hott

open algebra eq is_equiv equiv pointed function is_trunc nat

universe variable u

namespace group

  /- left and right actions -/
  definition is_equiv_mul_right_inf [constructor] {A : InfGroup} (a : A) : is_equiv (λb, b * a) :=
  adjointify _ (λb : A, b * a⁻¹) (λb, !inv_mul_cancel_right) (λb, !mul_inv_cancel_right)

  definition right_action_inf [constructor] {A : InfGroup} (a : A) : A ≃ A :=
  equiv.mk _ (is_equiv_mul_right_inf a)

  /- homomorphisms -/

  structure inf_homomorphism (G₁ G₂ : InfGroup) : Type :=
    (φ : G₁ → G₂)
    (p : is_mul_hom φ)

  infix ` →∞g `:55 := inf_homomorphism

  abbreviation inf_group_fun [unfold 3] [coercion] [reducible] := @inf_homomorphism.φ
  definition inf_homomorphism.struct [unfold 3] [instance] [priority 900] {G₁ G₂ : InfGroup}
    (φ : G₁ →∞g G₂) : is_mul_hom φ :=
  inf_homomorphism.p φ

  variables {G G₁ G₂ G₃ : InfGroup} {g h : G₁} {ψ : G₂ →∞g G₃} {φ₁ φ₂ : G₁ →∞g G₂} (φ : G₁ →∞g G₂)

  definition to_respect_mul_inf /- φ -/ (g h : G₁) : φ (g * h) = φ g * φ h :=
  respect_mul φ g h

  theorem to_respect_one_inf /- φ -/ : φ 1 = 1 :=
  have φ 1 * φ 1 = φ 1 * 1, by rewrite [-to_respect_mul_inf φ, +mul_one],
  eq_of_mul_eq_mul_left' this

  theorem to_respect_inv_inf /- φ -/ (g : G₁) : φ g⁻¹ = (φ g)⁻¹ :=
  have φ (g⁻¹) * φ g = 1, by rewrite [-to_respect_mul_inf φ, mul.left_inv, to_respect_one_inf φ],
  eq_inv_of_mul_eq_one this

  definition pmap_of_inf_homomorphism [constructor] /- φ -/ : G₁ →* G₂ :=
  pmap.mk φ begin exact to_respect_one_inf φ end

  definition inf_homomorphism_change_fun [constructor] {G₁ G₂ : InfGroup}
    (φ : G₁ →∞g G₂) (f : G₁ → G₂) (p : φ ~ f) : G₁ →∞g G₂ :=
  inf_homomorphism.mk f
    (λg h, (p (g * h))⁻¹ ⬝ to_respect_mul_inf φ g h ⬝ ap011 mul (p g) (p h))

  /- categorical structure of groups + homomorphisms -/

  definition inf_homomorphism_compose [constructor] [trans] [reducible]
    (ψ : G₂ →∞g G₃) (φ : G₁ →∞g G₂) : G₁ →∞g G₃ :=
  inf_homomorphism.mk (ψ ∘ φ) (is_mul_hom_compose _ _)

  variable (G)
  definition inf_homomorphism_id [constructor] [refl] : G →∞g G :=
  inf_homomorphism.mk (@id G) (is_mul_hom_id G)
  variable {G}

  abbreviation inf_gid [constructor] := @inf_homomorphism_id
  infixr ` ∘∞g `:75 := inf_homomorphism_compose

  structure inf_isomorphism (A B : InfGroup) :=
    (to_hom : A →∞g B)
    (is_equiv_to_hom : is_equiv to_hom)

  infix ` ≃∞g `:25 := inf_isomorphism
  attribute inf_isomorphism.to_hom [coercion]
  attribute inf_isomorphism.is_equiv_to_hom [instance]
  attribute inf_isomorphism._trans_of_to_hom [unfold 3]

  definition equiv_of_inf_isomorphism [constructor] (φ : G₁ ≃∞g G₂) : G₁ ≃ G₂ :=
  equiv.mk φ _

  definition pequiv_of_inf_isomorphism [constructor] (φ : G₁ ≃∞g G₂) :
    G₁ ≃* G₂ :=
  pequiv.mk φ begin esimp, exact _ end begin esimp, exact to_respect_one_inf φ end

  definition inf_isomorphism_of_equiv [constructor] (φ : G₁ ≃ G₂)
    (p : Πg₁ g₂, φ (g₁ * g₂) = φ g₁ * φ g₂) : G₁ ≃∞g G₂ :=
  inf_isomorphism.mk (inf_homomorphism.mk φ p) !to_is_equiv

  definition inf_isomorphism_of_eq [constructor] {G₁ G₂ : InfGroup} (φ : G₁ = G₂) : G₁ ≃∞g G₂ :=
  inf_isomorphism_of_equiv (equiv_of_eq (ap InfGroup.carrier φ))
    begin intros, induction φ, reflexivity end

  definition to_ginv_inf [constructor] (φ : G₁ ≃∞g G₂) : G₂ →∞g G₁ :=
  inf_homomorphism.mk φ⁻¹
    abstract begin
    intro g₁ g₂, apply inj' φ,
    rewrite [respect_mul φ, +right_inv φ]
    end end

  variable (G)
  definition inf_isomorphism.refl [refl] [constructor] : G ≃∞g G :=
  inf_isomorphism.mk !inf_gid !is_equiv_id
  variable {G}

  definition inf_isomorphism.symm [symm] [constructor] (φ : G₁ ≃∞g G₂) : G₂ ≃∞g G₁ :=
  inf_isomorphism.mk (to_ginv_inf φ) !is_equiv_inv

  definition inf_isomorphism.trans [trans] [constructor] (φ : G₁ ≃∞g G₂) (ψ : G₂ ≃∞g G₃) :
    G₁ ≃∞g G₃ :=
  inf_isomorphism.mk (ψ ∘∞g φ) (is_equiv_compose ψ φ _ _)

  definition inf_isomorphism.eq_trans [trans] [constructor]
     {G₁ G₂ : InfGroup} {G₃ : InfGroup} (φ : G₁ = G₂) (ψ : G₂ ≃∞g G₃) : G₁ ≃∞g G₃ :=
  proof inf_isomorphism.trans (inf_isomorphism_of_eq φ) ψ qed

  definition inf_isomorphism.trans_eq [trans] [constructor]
    {G₁ : InfGroup} {G₂ G₃ : InfGroup} (φ : G₁ ≃∞g G₂) (ψ : G₂ = G₃) : G₁ ≃∞g G₃ :=
  inf_isomorphism.trans φ (inf_isomorphism_of_eq ψ)

  postfix `⁻¹ᵍ⁸`:(max + 1) := inf_isomorphism.symm
  infixl ` ⬝∞g `:75 := inf_isomorphism.trans
  infixl ` ⬝∞gp `:75 := inf_isomorphism.trans_eq
  infixl ` ⬝∞pg `:75 := inf_isomorphism.eq_trans

  definition pmap_of_inf_isomorphism [constructor] (φ : G₁ ≃∞g G₂) : G₁ →* G₂ :=
  pequiv_of_inf_isomorphism φ

  definition to_fun_inf_isomorphism_trans {G H K : InfGroup} (φ : G ≃∞g H) (ψ : H ≃∞g K) :
    φ ⬝∞g ψ ~ ψ ∘ φ :=
  by reflexivity

  definition inf_homomorphism_mul [constructor] {G H : AbInfGroup} (φ ψ : G →∞g H) : G →∞g H :=
  inf_homomorphism.mk (λg, φ g * ψ g)
    abstract begin
      intro g g', refine ap011 mul !to_respect_mul_inf !to_respect_mul_inf ⬝ _,
      refine !mul.assoc ⬝ ap (mul _) (!mul.assoc⁻¹ ⬝ ap (λx, x * _) !mul.comm ⬝ !mul.assoc) ⬝
             !mul.assoc⁻¹
    end end

  definition trivial_inf_homomorphism (A B : InfGroup) : A →∞g B :=
  inf_homomorphism.mk (λa, 1) (λa a', (mul_one 1)⁻¹)

  /- given an equivalence A ≃ B we can transport a group structure on A to a group structure on B -/

  section

    parameters {A B : Type} (f : A ≃ B) (H : inf_group A)
    include H

    definition inf_group_equiv_mul (b b' : B) : B := f (f⁻¹ᶠ b * f⁻¹ᶠ b')

    definition inf_group_equiv_one : B := f one

    definition inf_group_equiv_inv (b : B) : B := f (f⁻¹ᶠ b)⁻¹

    local infix * := inf_group_equiv_mul
    local postfix ^ := inf_group_equiv_inv
    local notation 1 := inf_group_equiv_one

    theorem inf_group_equiv_mul_assoc (b₁ b₂ b₃ : B) : (b₁ * b₂) * b₃ = b₁ * (b₂ * b₃) :=
    by rewrite [↑inf_group_equiv_mul, +left_inv f, mul.assoc]

    theorem inf_group_equiv_one_mul (b : B) : 1 * b = b :=
    by rewrite [↑inf_group_equiv_mul, ↑inf_group_equiv_one, left_inv f, one_mul, right_inv f]

    theorem inf_group_equiv_mul_one (b : B) : b * 1 = b :=
    by rewrite [↑inf_group_equiv_mul, ↑inf_group_equiv_one, left_inv f, mul_one, right_inv f]

    theorem inf_group_equiv_mul_left_inv (b : B) : b^ * b = 1 :=
    by rewrite [↑inf_group_equiv_mul, ↑inf_group_equiv_one, ↑inf_group_equiv_inv,
                +left_inv f, mul.left_inv]

    definition inf_group_equiv_closed [constructor] : inf_group B :=
    ⦃inf_group,
      mul          := inf_group_equiv_mul,
      mul_assoc    := inf_group_equiv_mul_assoc,
      one          := inf_group_equiv_one,
      one_mul      := inf_group_equiv_one_mul,
      mul_one      := inf_group_equiv_mul_one,
      inv          := inf_group_equiv_inv,
      mul_left_inv := inf_group_equiv_mul_left_inv⦄

  end

  definition InfGroup_equiv_closed [constructor] (A : InfGroup) {B : Type} (f : A ≃ B) : InfGroup :=
  InfGroup.mk B (inf_group_equiv_closed f _)

  definition InfGroup_equiv_closed_isomorphism [constructor] (A : InfGroup) {B : Type} (f : A ≃ B) :
    A ≃∞g InfGroup_equiv_closed A f :=
  inf_isomorphism_of_equiv f (λa a', ap f (ap011 mul (to_left_inv f a) (to_left_inv f a'))⁻¹)

  section
    variables {A B : Type} (f : A ≃ B) (H : ab_inf_group A)
    include H
    definition inf_group_equiv_mul_comm (b b' : B) :
      inf_group_equiv_mul f _ b b' = inf_group_equiv_mul f _ b' b :=
    by rewrite [↑inf_group_equiv_mul, mul.comm]

    definition ab_inf_group_equiv_closed : ab_inf_group B :=
    ⦃ ab_inf_group, inf_group_equiv_closed f _, mul_comm := inf_group_equiv_mul_comm f H ⦄
  end

  variable (G)

  /- the trivial ∞-group -/
  open unit
  definition inf_group_unit [constructor] : inf_group unit :=
  inf_group.mk (λx y, star) (λx y z, idp) star (unit.rec idp) (unit.rec idp) (λx, star) (λx, idp)

  definition ab_inf_group_unit [constructor] : ab_inf_group unit :=
  ⦃ab_inf_group, inf_group_unit, mul_comm := λx y, idp⦄

  definition trivial_inf_group [constructor] : InfGroup :=
  InfGroup.mk _ inf_group_unit

  definition AbInfGroup_of_InfGroup (G : InfGroup.{u}) (H : Π x y : G, x * y = y * x) :
    AbInfGroup.{u} :=
  begin
    induction G,
    fapply AbInfGroup.mk,
    assumption,
    exact ⦃ab_inf_group, struct', mul_comm := H⦄
  end

  definition trivial_ab_inf_group : AbInfGroup.{0} :=
  begin
    fapply AbInfGroup_of_InfGroup trivial_inf_group, intro x y, reflexivity
  end

  definition trivial_inf_group_of_is_contr [H : is_contr G] : G ≃∞g trivial_inf_group :=
  begin
    fapply inf_isomorphism_of_equiv,
    { exact equiv_unit_of_is_contr _ _ },
    { intros, reflexivity}
  end

  definition ab_inf_group_of_is_contr (A : Type) (H : is_contr A) : ab_inf_group A :=
  have ab_inf_group unit, from ab_inf_group_unit,
  ab_inf_group_equiv_closed (equiv_unit_of_is_contr A _)⁻¹ᵉ _

  definition inf_group_of_is_contr (A : Type) (H : is_contr A) : inf_group A :=
  have ab_inf_group A, from ab_inf_group_of_is_contr A H, by exact _

  definition ab_inf_group_lift_unit : ab_inf_group (lift unit) :=
  ab_inf_group_of_is_contr (lift unit) _

  definition trivial_ab_inf_group_lift : AbInfGroup :=
  AbInfGroup.mk _ ab_inf_group_lift_unit

  definition from_trivial_ab_inf_group (A : AbInfGroup) : trivial_ab_inf_group →∞g A :=
  trivial_inf_homomorphism trivial_ab_inf_group A

  definition to_trivial_ab_inf_group (A : AbInfGroup) : A →∞g trivial_ab_inf_group :=
  trivial_inf_homomorphism A trivial_ab_inf_group

  /- infinity pgroups are infgroups where 1 is definitionally the point of X -/

  structure inf_pgroup [class] (X : Type*) extends inf_semigroup X, has_inv X :=
    (pt_mul : Πa, mul pt a = a)
    (mul_pt : Πa, mul a pt = a)
    (mul_left_inv_pt : Πa, mul (inv a) a = pt)

  definition pt_mul (X : Type*) [inf_pgroup X] (x : X) : pt * x = x := inf_pgroup.pt_mul x
  definition mul_pt (X : Type*) [inf_pgroup X] (x : X) : x * pt = x := inf_pgroup.mul_pt x
  definition mul_left_inv_pt (X : Type*) [inf_pgroup X] (x : X) : x⁻¹ * x = pt :=
  inf_pgroup.mul_left_inv_pt x

  definition inf_group_of_inf_pgroup [reducible] [instance] (X : Type*) [H : inf_pgroup X]
    : inf_group X :=
  ⦃inf_group, H,
          one := pt,
          one_mul := inf_pgroup.pt_mul ,
          mul_one := inf_pgroup.mul_pt,
          mul_left_inv := inf_pgroup.mul_left_inv_pt⦄

  definition inf_pgroup_of_inf_group (X : Type*) [H : inf_group X] (p : one = pt :> X) :
    inf_pgroup X :=
  begin
    cases X with X x, esimp at *, induction p,
    exact ⦃inf_pgroup, H,
            pt_mul := one_mul,
            mul_pt := mul_one,
            mul_left_inv_pt := mul.left_inv⦄
  end

  definition inf_Group_of_inf_pgroup (G : Type*) [inf_pgroup G] : InfGroup :=
  InfGroup.mk G _

  definition inf_pgroup_InfGroup [instance] (G : InfGroup) : inf_pgroup G :=
  ⦃ inf_pgroup, InfGroup.struct G,
    pt_mul := one_mul,
    mul_pt := mul_one,
    mul_left_inv_pt := mul.left_inv ⦄

  section

    parameters {A B : Type*} (f : A ≃* B) (s : inf_pgroup A)
    include s

    definition inf_pgroup_pequiv_mul (b b' : B) : B := f (f⁻¹ᶠ b * f⁻¹ᶠ b')

    definition inf_pgroup_pequiv_inv (b : B) : B := f (f⁻¹ᶠ b)⁻¹

    local infix * := inf_pgroup_pequiv_mul
    local postfix ^ := inf_pgroup_pequiv_inv

    theorem inf_pgroup_pequiv_mul_assoc (b₁ b₂ b₃ : B) : (b₁ * b₂) * b₃ = b₁ * (b₂ * b₃) :=
    begin
      refine ap (λa, f (mul a _)) (left_inv f _) ⬝ _ ⬝ ap (λa, f (mul _ a)) (left_inv f _)⁻¹,
      exact ap f !mul.assoc
    end

    theorem inf_pgroup_pequiv_pt_mul (b : B) : pt * b = b :=
    by rewrite [↑inf_pgroup_pequiv_mul, respect_pt, pt_mul]; apply right_inv f

    theorem inf_pgroup_pequiv_mul_pt (b : B) : b * pt = b :=
    by rewrite [↑inf_pgroup_pequiv_mul, respect_pt, mul_pt]; apply right_inv f

    theorem inf_pgroup_pequiv_mul_left_inv_pt (b : B) : b^ * b = pt :=
    begin
      refine ap (λa, f (mul a _)) (left_inv f _) ⬝ _,
      exact ap f !mul_left_inv_pt ⬝ !respect_pt,
    end

    definition inf_pgroup_pequiv_closed : inf_pgroup B :=
    ⦃inf_pgroup,
      mul          := inf_pgroup_pequiv_mul,
      mul_assoc    := inf_pgroup_pequiv_mul_assoc,
      pt_mul       := inf_pgroup_pequiv_pt_mul,
      mul_pt       := inf_pgroup_pequiv_mul_pt,
      inv          := inf_pgroup_pequiv_inv,
      mul_left_inv_pt := inf_pgroup_pequiv_mul_left_inv_pt⦄

  end

  /- infgroup from loop spaces -/

  definition inf_pgroup_loop [constructor] [instance] (A : Type*) : inf_pgroup (Ω A) :=
  inf_pgroup.mk concat con.assoc inverse idp_con con_idp con.left_inv

  definition inf_group_loop [constructor] (A : Type*) : inf_group (Ω A) := _

  definition ab_inf_group_loop [constructor] [instance] (A : Type*) : ab_inf_group (Ω (Ω A)) :=
  ⦃ab_inf_group, inf_group_loop _, mul_comm := eckmann_hilton⦄

  definition inf_group_loopn (n : ℕ) (A : Type*) [H : is_succ n] : inf_group (Ω[n] A) :=
  by induction H; exact _

  definition ab_inf_group_loopn (n : ℕ) (A : Type*) [H : is_at_least_two n] :
    ab_inf_group (Ω[n] A) :=
  by induction H; exact _

  definition gloop [constructor] (A : Type*) : InfGroup :=
  InfGroup.mk (Ω A) (inf_group_loop A)

  definition gloopn (n : ℕ) [H : is_succ n] (A : Type*) : InfGroup :=
  InfGroup.mk (Ω[n] A) (inf_group_loopn n A)

  definition agloopn (n : ℕ) [H : is_at_least_two n] (A : Type*) : AbInfGroup :=
  AbInfGroup.mk (Ω[n] A) (ab_inf_group_loopn n A)

  definition gloopn' (n : ℕ) (A : InfGroup) : InfGroup :=
  InfGroup.mk (Ω[n] A) (by cases n; exact InfGroup.struct A; apply inf_group_loopn)

  notation `Ωg` := gloop
  notation `Ωg[`:95 n:0 `]`:0 := gloopn n
  notation `Ωag[`:95 n:0 `]`:0 := agloopn n
  notation `Ωg'[`:95 n:0 `]`:0 := gloopn' n

  definition gap1 {A B : Type*} (f : A →* B) : Ωg A →∞g Ωg B :=
  inf_homomorphism.mk (Ω→ f) (ap1_con f)

  definition gapn (n : ℕ) [H : is_succ n] {A B : Type*} (f : A →* B) : Ωg[n] A →∞g Ωg[n] B :=
  inf_homomorphism.mk (Ω→[n] f) (by induction H with n; exact apn_con n f)

  definition gapn' (n : ℕ) {A B : InfGroup} (f : A →∞g B) : Ωg'[n] A →∞g Ωg'[n] B :=
  inf_homomorphism.mk (Ω→[n] (pmap_of_inf_homomorphism f))
    (by cases n with n; exact inf_homomorphism.struct f; exact apn_con n (pmap_of_inf_homomorphism f))

  notation `Ωg→` := gap1
  notation `Ωg→[`:95 n:0 `]`:0 := gapn n
  notation `Ωg'→[`:95 n:0 `]`:0 := gapn' n

  definition gloop_isomorphism_gloop {A B : Type*} (f : A ≃* B) : Ωg A ≃∞g Ωg B :=
  inf_isomorphism.mk (Ωg→ f) (to_is_equiv (loop_pequiv_loop f))

  definition gloopn_isomorphism_gloopn (n : ℕ) [H : is_succ n] {A B : Type*} (f : A ≃* B) :
    Ωg[n] A ≃∞g Ωg[n] B :=
  inf_isomorphism.mk (Ωg→[n] f) (to_is_equiv (loopn_pequiv_loopn n f))

  notation `Ωg≃` := gloop_isomorphism_gloop
  notation `Ωg≃[`:95 n:0 `]`:0 := gloopn_isomorphism_gloopn

  definition gloopn_succ_in (n : ℕ) [H : is_succ n] (A : Type*) : Ωg[succ n] A ≃∞g Ωg[n] (Ω A) :=
  inf_isomorphism_of_equiv (loopn_succ_in n A) (by induction H with n; exact loopn_succ_in_con)

end group
