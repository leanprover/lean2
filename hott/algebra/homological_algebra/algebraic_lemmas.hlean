/-
Copyright (c) 2017 Sayantan Khan
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sayantan Khan

Proofs of elementary algebraic lemmas.
-/

import algebra.group_theory

open algebra
open group

lemma transport_equality_hom : Π {G₁ G₂ : AbGroup}, Π (φ : homomorphism (G₁) (G₂)), Π {x y : G₁},
  (x = y) → (φ(x) = φ(y)) :=
    λ G₁ G₂ φ x, @eq.rec(_)(x)(_) (eq.refl(group_fun φ(x)))

lemma transport_equality_left_mul : Π {G : AbGroup}, Π (l : G), Π {x y : G},
  (x = y) → (l*x = l*y) :=
    λ G l x, @eq.rec(_)(x)(_) (eq.refl(l*x))

lemma transport_equality_right_mul : Π {G : AbGroup}, Π (r : G), Π {x y : G},
  (x = y) → (x*r = y*r) :=
    λ G r x, @eq.rec(_)(x)(_) (eq.refl(x*r))
    
lemma mul_inverse : Π {G : AbGroup}, Π (x : G), (x⁻¹)*x = group.one(G) := λ G x, ab_group.mul_left_inv x

lemma inverse_inverse : Π {G : AbGroup}, Π (x : G), (x⁻¹)⁻¹ = x :=
  λ G x, inv_inv(x)

lemma mul_commutative : Π {G : AbGroup}, Π (x y : G), x*y = y*x :=
  λ G x y, ab_group.mul_comm x y

lemma mul_associative : Π {G : AbGroup}, Π (x y z : G), (x*y)*z = x*(y*z) :=
  λ G x y z, ab_group.mul_assoc x y z
  
lemma mul_respects_one : Π {G : AbGroup}, Π (x : G),
  1*x = x := λ G x, ab_group.one_mul x

lemma cancelling : Π {G : AbGroup}, Π (x y : G), (x = y) → (y⁻¹*x = 1) :=
  λ G x y proofEq,
    eq.trans (transport_equality_left_mul (y⁻¹) (proofEq)) (mul_inverse(y))

lemma hom_respects_one : Π {G₁ G₂ : AbGroup}, Π (φ : homomorphism (G₁) (G₂)), Π (x : G₁),
  (x = group.one(G₁)) → (φ(x) = group.one(G₂)) :=
    λ G₁ G₂ φ x proofOfOne, eq.trans (transport_equality_hom (φ)(proofOfOne)) (respect_one φ)

lemma hom_respects_mul : Π {G₁ G₂ : AbGroup}, Π (φ : homomorphism (G₁) (G₂)), Π (x y : G₁),
  φ(x*y) = φ(x)*φ(y) :=
    λ G₁ G₂ φ x y, to_respect_mul φ x y

lemma hom_respects_inv : Π {G₁ G₂ : AbGroup}, Π (φ : homomorphism (G₁) (G₂)), Π (x : G₁),
  φ(x⁻¹) = (φ(x))⁻¹ :=
    λ G₁ G₂ φ x, to_respect_inv φ x

lemma hom_respects_cancelling : Π {G₁ G₂ : AbGroup}, Π (φ : homomorphism (G₁) (G₂)), Π {x y : G₁},
  (φ(x) = φ(y)) → φ(y⁻¹*x) = 1 :=
    λ G₁ G₂ φ x y proofEq,
    eq.trans 
    (eq.trans (hom_respects_mul (φ) (y⁻¹) (x)) (transport_equality_right_mul (group_fun (φ) (x)) (hom_respects_inv(φ)(y)))) 
    (eq.trans (transport_equality_left_mul((group_fun (φ) (y))⁻¹)(proofEq))
    (mul_inverse(group_fun (φ) (y))))

/-
This was supposed to be a lemma: compiling the proof however led to
unification errors which I could not debug. Setting this as an axiom
is a temporary workaround.
-/
axiom combine_terms : Π {G₁ G₂ : AbGroup}, Π (φ : homomorphism (G₁) (G₂)), Π (a c : G₁), Π (b : G₂),
  φ(a) = b⁻¹*φ(c) → b = φ(a⁻¹*c) 
