/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

truncating an ∞-group to a group
-/

import hit.trunc algebra.bundled

open eq is_trunc trunc

namespace algebra

  section
  parameters (n : trunc_index) {A : Type} [inf_group A]

  local abbreviation G := trunc n A

  definition trunc_mul [unfold 9 10] (g h : G) : G :=
  begin
    induction g with p,
    induction h with q,
    exact tr (p * q)
  end

  definition trunc_inv [unfold 9] (g : G) : G :=
  begin
    induction g with p,
    exact tr p⁻¹
  end

  definition trunc_one [constructor] : G :=
  tr 1

  local notation 1 := trunc_one
  local postfix ⁻¹ := trunc_inv
  local infix * := trunc_mul

  theorem trunc_mul_assoc (g₁ g₂ g₃ : G) : g₁ * g₂ * g₃ = g₁ * (g₂ * g₃) :=
  begin
    induction g₁ with p₁,
    induction g₂ with p₂,
    induction g₃ with p₃,
    exact ap tr !mul.assoc,
  end

  theorem trunc_one_mul (g : G) : 1 * g = g :=
  begin
    induction g with p,
    exact ap tr !one_mul
  end

  theorem trunc_mul_one (g : G) : g * 1 = g :=
  begin
    induction g with p,
    exact ap tr !mul_one
  end

  theorem trunc_mul_left_inv (g : G) : g⁻¹ * g = 1 :=
  begin
    induction g with p,
    exact ap tr !mul.left_inv
  end

  parameter (A)
  definition inf_group_trunc [constructor] [instance] : inf_group (trunc n A) :=
  ⦃inf_group,
    mul          := algebra.trunc_mul          n,
    mul_assoc    := algebra.trunc_mul_assoc    n,
    one          := algebra.trunc_one          n,
    one_mul      := algebra.trunc_one_mul      n,
    mul_one      := algebra.trunc_mul_one      n,
    inv          := algebra.trunc_inv          n,
    mul_left_inv := algebra.trunc_mul_left_inv n⦄

  definition group_trunc [constructor] : group (trunc 0 A) :=
  group_of_inf_group _

  end

  definition igtrunc [constructor] (n : ℕ₋₂) (A : InfGroup) : InfGroup :=
  InfGroup.mk (trunc n A) (inf_group_trunc n A)

  definition gtrunc [constructor] (A : InfGroup) : Group :=
  Group.mk (trunc 0 A) (group_trunc A)

  section
  variables (n : trunc_index) {A : Type} [ab_inf_group A]

  theorem trunc_mul_comm (g h : trunc n A) : trunc_mul n g h = trunc_mul n h g :=
  begin
    induction g with p,
    induction h with q,
    exact ap tr !mul.comm
  end

  variable (A)
  definition ab_inf_group_trunc [constructor] [instance] : ab_inf_group (trunc n A) :=
  ⦃ab_inf_group, inf_group_trunc n A, mul_comm := algebra.trunc_mul_comm n⦄

  definition ab_group_trunc [constructor] : ab_group (trunc 0 A) :=
  ab_group_of_ab_inf_group _

  definition aigtrunc [constructor] (n : ℕ₋₂) (A : AbInfGroup) : AbInfGroup :=
  AbInfGroup.mk (trunc n A) (ab_inf_group_trunc n A)

  definition agtrunc [constructor] (A : AbInfGroup) : AbGroup :=
  AbGroup.mk (trunc 0 A) (ab_group_trunc A)

  end

end algebra
