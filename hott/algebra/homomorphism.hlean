/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Homomorphisms between structures.
-/
import algebra.ring algebra.category.category
open eq function is_trunc

namespace algebra

/- additive structures -/

variables {A B C : Type}

definition is_add_hom [class] [has_add A] [has_add B] (f : A → B) : Type :=
∀ a₁ a₂, f (a₁ + a₂) = f a₁ + f a₂

definition respect_add [has_add A] [has_add B] (f : A → B) [H : is_add_hom f] (a₁ a₂ : A) :
  f (a₁ + a₂) = f a₁ + f a₂ := H a₁ a₂

definition is_prop_is_add_hom [instance] [has_add A] [has_add B] [is_set B] (f : A → B) :
  is_prop (is_add_hom f) :=
by unfold is_add_hom; apply _

definition is_add_hom_id (A : Type) [has_add A] : is_add_hom (@id A) :=
take a₁ a₂, rfl

definition is_add_hom_compose [has_add A] [has_add B] [has_add C]
  (f : B → C) (g : A → B) [is_add_hom f] [is_add_hom g] : is_add_hom (f ∘ g) :=
take a₁ a₂, begin esimp, rewrite [respect_add g, respect_add f] end

section add_group_A_B
  variables [add_group A] [add_group B]

  definition respect_zero (f : A → B) [is_add_hom f] :
    f (0 : A) = 0 :=
  have f 0 + f 0 = f 0 + 0, by rewrite [-respect_add f, +add_zero],
  eq_of_add_eq_add_left this

  definition respect_neg (f : A → B) [is_add_hom f] (a : A) :
    f (- a) = - f a :=
  have f (- a) + f a = 0, by rewrite [-respect_add f, add.left_inv, respect_zero f],
  eq_neg_of_add_eq_zero this

  definition respect_sub (f : A → B) [is_add_hom f] (a₁ a₂ : A) :
    f (a₁ - a₂) = f a₁ - f a₂ :=
  by rewrite [*sub_eq_add_neg, *(respect_add f), (respect_neg f)]

  definition is_embedding_of_is_add_hom [add_group B] (f : A → B) [is_add_hom f]
      (H : ∀ x, f x = 0 → x = 0) :
    is_embedding f :=
  is_embedding_of_is_injective
    (take x₁ x₂,
      suppose f x₁ = f x₂,
      have f (x₁ - x₂) = 0, by rewrite [respect_sub f, this, sub_self],
      have x₁ - x₂ = 0, from H _ this,
      eq_of_sub_eq_zero this)

  definition eq_zero_of_is_add_hom [add_group B] {f : A → B} [is_add_hom f]
      [is_embedding f] {a : A} (fa0 : f a = 0) :
    a = 0 :=
  have f a = f 0, by rewrite [fa0, respect_zero f],
  show a = 0, from is_injective_of_is_embedding this
end add_group_A_B

/- multiplicative structures -/

definition is_mul_hom [class] [has_mul A] [has_mul B] (f : A → B) : Type :=
∀ a₁ a₂, f (a₁ * a₂) = f a₁ * f a₂

definition respect_mul [has_mul A] [has_mul B] (f : A → B) [H : is_mul_hom f] (a₁ a₂ : A) :
  f (a₁ * a₂) = f a₁ * f a₂ := H a₁ a₂

definition is_prop_is_mul_hom [instance] [has_mul A] [has_mul B] [is_set B] (f : A → B) :
  is_prop (is_mul_hom f) :=
begin unfold is_mul_hom, apply _ end

definition is_mul_hom_id (A : Type) [has_mul A] : is_mul_hom (@id A) :=
take a₁ a₂, rfl

definition is_mul_hom_compose [has_mul A] [has_mul B] [has_mul C]
  (f : B → C) (g : A → B) [is_mul_hom f] [is_mul_hom g] : is_mul_hom (f ∘ g) :=
take a₁ a₂, begin esimp, rewrite [respect_mul g, respect_mul f] end

section group_A_B
  variables [group A] [group B]

  definition respect_one (f : A → B) [is_mul_hom f] :
    f (1 : A) = 1 :=
  have f 1 * f 1 = f 1 * 1, by rewrite [-respect_mul f, *mul_one],
  eq_of_mul_eq_mul_left' this

  definition respect_inv (f : A → B) [is_mul_hom f] (a : A) :
    f (a⁻¹) = (f a)⁻¹ :=
  have f (a⁻¹) * f a = 1, by rewrite [-respect_mul f, mul.left_inv, respect_one f],
  eq_inv_of_mul_eq_one this

  definition is_embedding_of_is_mul_hom [group B] (f : A → B) [is_mul_hom f]
      (H : ∀ x, f x = 1 → x = 1) :
    is_embedding f :=
  is_embedding_of_is_injective
    (take x₁ x₂,
      suppose f x₁ = f x₂,
      have f (x₁ * x₂⁻¹) = 1, by rewrite [respect_mul f, respect_inv f, this, mul.right_inv],
      have x₁ * x₂⁻¹ = 1, from H _ this,
      eq_of_mul_inv_eq_one this)

  definition eq_one_of_is_mul_hom [add_group B] {f : A → B} [is_mul_hom f]
      [is_embedding f] {a : A} (fa1 : f a = 1) :
    a = 1 :=
  have f a = f 1, by rewrite [fa1, respect_one f],
  show a = 1, from is_injective_of_is_embedding this
end group_A_B

/- rings -/

definition is_ring_hom [class] {R₁ R₂ : Type} [semiring R₁] [semiring R₂] (f : R₁ → R₂) :=
is_add_hom f × is_mul_hom f × f 1 = 1

definition is_ring_hom.mk {R₁ R₂ : Type} [semiring R₁] [semiring R₂] (f : R₁ → R₂)
    (h₁ : is_add_hom f) (h₂ : is_mul_hom f) (h₃ : f 1 = 1) : is_ring_hom f :=
pair h₁ (pair h₂ h₃)

definition is_add_hom_of_is_ring_hom [instance] {R₁ R₂ : Type} [semiring R₁] [semiring R₂]
    (f : R₁ → R₂) [H : is_ring_hom f] : is_add_hom f :=
prod.pr1 H

definition is_mul_hom_of_is_ring_hom [instance] {R₁ R₂ : Type} [semiring R₁] [semiring R₂]
    (f : R₁ → R₂) [H : is_ring_hom f] : is_mul_hom f :=
prod.pr1 (prod.pr2 H)

definition is_ring_hom.respect_one {R₁ R₂ : Type} [semiring R₁] [semiring R₂]
    (f : R₁ → R₂) [H : is_ring_hom f] : f 1 = 1 :=
prod.pr2 (prod.pr2 H)

definition is_prop_is_ring_hom [instance] {R₁ R₂ : Type} [semiring R₁] [semiring R₂] (f : R₁ → R₂) :
  is_prop (is_ring_hom f) :=
have h₁ : is_prop (is_add_hom f), from _,
have h₂ : is_prop (is_mul_hom f), from _,
have h₃ : is_prop (f 1 = 1), from _,
begin unfold is_ring_hom, apply _ end

section semiring
  variables {R₁ R₂ R₃ : Type} [semiring R₁] [semiring R₂] [semiring R₃]
  variables (g : R₂ → R₃) (f : R₁ → R₂) [is_ring_hom g] [is_ring_hom f]

  definition is_ring_hom_id : is_ring_hom (@id R₁) :=
  is_ring_hom.mk id (λ a₁ a₂, rfl) (λ a₁ a₂, rfl) rfl

  definition is_ring_hom_comp : is_ring_hom (g ∘ f) :=
  is_ring_hom.mk _
    (take a₁ a₂, begin esimp, rewrite [respect_add f, respect_add g] end)
    (take r a, by esimp; rewrite [respect_mul f, respect_mul g])
    (by esimp; rewrite *is_ring_hom.respect_one)

  definition respect_mul_add_mul (a b c d : R₁) : f (a * b + c * d) = f a * f b + f c * f d :=
  by rewrite [respect_add f, +(respect_mul f)]
end semiring

end algebra
