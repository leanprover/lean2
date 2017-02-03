/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura

Various multiplicative and additive structures. Partially modeled on Isabelle's library.
-/

import algebra.inf_group

open eq eq.ops   -- note: ⁻¹ will be overloaded
open binary algebra is_trunc
set_option class.force_new true

variable {A : Type}

/- semigroup -/

namespace algebra

structure is_set_structure [class] (A : Type) :=
  (is_set_carrier : is_set A)

attribute is_set_structure.is_set_carrier [instance] [priority 950]

structure semigroup [class] (A : Type) extends is_set_structure A, inf_semigroup A

structure comm_semigroup [class] (A : Type) extends semigroup A, comm_inf_semigroup A

structure left_cancel_semigroup [class] (A : Type) extends semigroup A, left_cancel_inf_semigroup A

structure right_cancel_semigroup [class] (A : Type) extends semigroup A, right_cancel_inf_semigroup A

/- additive semigroup -/

definition add_semigroup [class] : Type → Type := semigroup

definition add_semigroup.is_set_carrier [instance] [priority 900] (A : Type) [H : add_semigroup A] :
  is_set A :=
@is_set_structure.is_set_carrier A (@semigroup.to_is_set_structure A H)

definition add_inf_semigroup_of_add_semigroup [reducible] [trans_instance] (A : Type)
  [H : add_semigroup A] : add_inf_semigroup A :=
@semigroup.to_inf_semigroup A H

definition add_comm_semigroup [class] : Type → Type := comm_semigroup

definition add_semigroup_of_add_comm_semigroup [reducible] [trans_instance] (A : Type)
  [H : add_comm_semigroup A] : add_semigroup A :=
@comm_semigroup.to_semigroup A H

definition add_comm_inf_semigroup_of_add_comm_semigroup [reducible] [trans_instance] (A : Type)
  [H : add_comm_semigroup A] : add_comm_inf_semigroup A :=
@comm_semigroup.to_comm_inf_semigroup A H

definition add_left_cancel_semigroup [class] : Type → Type := left_cancel_semigroup

definition add_semigroup_of_add_left_cancel_semigroup [reducible] [trans_instance] (A : Type)
  [H : add_left_cancel_semigroup A] : add_semigroup A :=
@left_cancel_semigroup.to_semigroup A H

definition add_left_cancel_inf_semigroup_of_add_left_cancel_semigroup [reducible] [trans_instance]
  (A : Type) [H : add_left_cancel_semigroup A] : add_left_cancel_inf_semigroup A :=
@left_cancel_semigroup.to_left_cancel_inf_semigroup A H

definition add_right_cancel_semigroup [class] : Type → Type := right_cancel_semigroup

definition add_semigroup_of_add_right_cancel_semigroup [reducible] [trans_instance] (A : Type)
  [H : add_right_cancel_semigroup A] : add_semigroup A :=
@right_cancel_semigroup.to_semigroup A H

definition add_right_cancel_inf_semigroup_of_add_right_cancel_semigroup [reducible] [trans_instance]
  (A : Type) [H : add_right_cancel_semigroup A] : add_right_cancel_inf_semigroup A :=
@right_cancel_semigroup.to_right_cancel_inf_semigroup A H

/- monoid -/

structure monoid [class] (A : Type) extends semigroup A, inf_monoid A

structure comm_monoid [class] (A : Type) extends monoid A, comm_semigroup A, comm_inf_monoid A

/- additive monoid -/

definition add_monoid [class] : Type → Type := monoid

definition add_semigroup_of_add_monoid [reducible] [trans_instance] (A : Type)
  [H : add_monoid A] : add_semigroup A :=
@monoid.to_semigroup A H

definition add_inf_monoid_of_add_monoid [reducible] [trans_instance] (A : Type)
  [H : add_monoid A] : add_inf_monoid A :=
@monoid.to_inf_monoid A H

definition add_comm_monoid [class] : Type → Type := comm_monoid

definition add_monoid_of_add_comm_monoid [reducible] [trans_instance] (A : Type)
  [H : add_comm_monoid A] : add_monoid A :=
@comm_monoid.to_monoid A H

definition add_comm_semigroup_of_add_comm_monoid [reducible] [trans_instance] (A : Type)
  [H : add_comm_monoid A] : add_comm_semigroup A :=
@comm_monoid.to_comm_semigroup A H

definition add_comm_inf_monoid_of_add_comm_monoid [reducible] [trans_instance] (A : Type)
  [H : add_comm_monoid A] : add_comm_inf_monoid A :=
@comm_monoid.to_comm_inf_monoid A H

definition add_monoid.to_monoid {A : Type} [s : add_monoid A] : monoid A := s
definition add_comm_monoid.to_comm_monoid {A : Type} [s : add_comm_monoid A] : comm_monoid A := s
definition monoid.to_add_monoid {A : Type} [s : monoid A] : add_monoid A := s
definition comm_monoid.to_add_comm_monoid {A : Type} [s : comm_monoid A] : add_comm_monoid A := s

/- group -/

structure group [class] (A : Type) extends monoid A, inf_group A

definition group_of_inf_group (A : Type) [s : inf_group A] [is_set A] : group A :=
⦃group, s, is_set_carrier := _⦄

section group

  variable [s : group A]
  include s

  definition group.to_left_cancel_semigroup [trans_instance] : left_cancel_semigroup A :=
  ⦃ left_cancel_semigroup, s,
    mul_left_cancel := @mul_left_cancel A _ ⦄

  definition group.to_right_cancel_semigroup [trans_instance] : right_cancel_semigroup A :=
  ⦃ right_cancel_semigroup, s,
    mul_right_cancel := @mul_right_cancel A _ ⦄

end group

structure ab_group [class] (A : Type) extends group A, comm_monoid A, ab_inf_group A

definition ab_group_of_ab_inf_group (A : Type) [s : ab_inf_group A] [is_set A] : ab_group A :=
⦃ab_group, s, is_set_carrier := _⦄

/- additive group -/

definition add_group [class] : Type → Type := group

definition add_semigroup_of_add_group [reducible] [trans_instance] (A : Type)
  [H : add_group A] : add_monoid A :=
@group.to_monoid A H

definition add_inf_group_of_add_group [reducible] [trans_instance] (A : Type)
  [H : add_group A] : add_inf_group A :=
@group.to_inf_group A H

definition add_group.to_group {A : Type} [s : add_group A] : group A := s
definition group.to_add_group {A : Type} [s : group A] : add_group A := s

definition add_group_of_add_inf_group (A : Type) [s : add_inf_group A] [is_set A] :
  add_group A :=
⦃group, s, is_set_carrier := _⦄

section add_group

  variables [s : add_group A]
  include s

  definition add_group.to_add_left_cancel_semigroup [reducible] [trans_instance] :
    add_left_cancel_semigroup A :=
  @group.to_left_cancel_semigroup A s

  definition add_group.to_add_right_cancel_semigroup [reducible] [trans_instance] :
    add_right_cancel_semigroup A :=
  @group.to_right_cancel_semigroup A s

end add_group

definition add_ab_group [class] : Type → Type := ab_group

definition add_group_of_add_ab_group [reducible] [trans_instance] (A : Type)
  [H : add_ab_group A] : add_group A :=
@ab_group.to_group A H

definition add_comm_monoid_of_add_ab_group [reducible] [trans_instance] (A : Type)
  [H : add_ab_group A] : add_comm_monoid A :=
@ab_group.to_comm_monoid A H

definition add_ab_inf_group_of_add_ab_group [reducible] [trans_instance] (A : Type)
  [H : add_ab_group A] : add_ab_inf_group A :=
@ab_group.to_ab_inf_group A H

definition add_ab_group.to_ab_group {A : Type} [s : add_ab_group A] : ab_group A := s
definition ab_group.to_add_ab_group {A : Type} [s : ab_group A] : add_ab_group A := s

definition add_ab_group_of_add_ab_inf_group (A : Type) [s : add_ab_inf_group A] [is_set A] :
  add_ab_group A :=
⦃ab_group, s, is_set_carrier := _⦄

definition group_of_add_group (A : Type) [G : add_group A] : group A :=
⦃group,
  mul             := has_add.add,
  mul_assoc       := add.assoc,
  one             := !has_zero.zero,
  one_mul         := zero_add,
  mul_one         := add_zero,
  inv             := has_neg.neg,
  mul_left_inv    := add.left_inv,
  is_set_carrier := _⦄

end algebra
open algebra
