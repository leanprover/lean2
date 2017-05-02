/-
Copyright (c) 2017 Sayantan Khan
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sayantan Khan

Proofs of elementary lemmas.
-/

import algebra.group_theory
import .chain_complex_abelian_group

open int
open sigma.ops
open algebra
open group
open abelian_chain_complex
open abelian_chain_complex.ab_exact_chain_complex
open abelian_chain_complex.exact_chain_map

set_option unifier.max_steps 1000000

/-
Auxiliary lemmas. May be moved somewhere else.
-/

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

axiom combine_terms : Π {G₁ G₂ : AbGroup}, Π (φ : homomorphism (G₁) (G₂)), Π (a c : G₁), Π (b : G₂),
  φ(a) = b⁻¹*φ(c) → b = φ(a⁻¹*c) 

-- lemma combine_terms : Π {G₁ G₂ : AbGroup}, Π (φ : homomorphism (G₁) (G₂)), Π (a b : G₁), Π (c : G₂),
--   φ(a)*φ(b) = c → c = φ(a*b) :=
--     λ G₁ G₂ φ a b c proofEq,
--     eq.symm (eq.trans (hom_respects_mul (φ) (a) (b)) (proofEq))

-- lemma take_over : Π {G₁ G₂ : AbGroup}, Π (φ : homomorphism (G₁) (G₂)), Π (a c : G₁), Π (b : G₂),
--   φ(a) = b⁻¹ * φ(c) → b*φ(a) = φ(c) :=
--     λ G₁ G₂ φ a c b proofEq,
--     eq.trans
--     (transport_equality_right_mul (group_fun (φ) (a)) (eq.symm (inverse_inverse(b))))
--     (transport_equality_left_mul ((b⁻¹)⁻¹) (proofEq))

/-
Simple lemma showing surjective and injective imply bijective.
-/
lemma surjective_and_injective_imply_bijective : Π {G₁ G₂ : AbGroup}, Π {φ : homomorphism (G₁) (G₂)},
  surjective_map (φ) → injective_map (φ) → bijective_map (φ) :=
    λ G₁ G₂ φ proofSurj proofInj, bijective_map.mk
      (surjective_map.get_preimage(proofSurj))
      (injective_map.comes_from_zero(proofInj))

/-
Proof of the the fact the if 0 → A → B is exact, then the map
from A to B is injective.
-/
theorem left_zero_implies_injective : Π (C : ab_exact_chain_complex), Π (z : ℤ),
  zero_map(boundary_map(C)(z)) → injective_map(boundary_map(C)(z-1)) :=
    λ C z pZeroMap, injective_map.mk 
      (λ x pGoesZero,
        ((
        λ proofPreImage,
          (
            eq.trans (eq.symm (pr₂(proofPreImage))) (zero_map.goes_to_zero(pZeroMap)(pr₁(proofPreImage)))
          )
        )
        (exactness(C)(z)(x)(pGoesZero)))
      )
      
/-
Proof of the fact that if A → B → 0 is exact, then the map
from A to B is surjective
-/
theorem right_zero_implies_surjective : Π (C : ab_exact_chain_complex), Π (z : ℤ),
  zero_map(boundary_map(C)(z-1)) → surjective_map(boundary_map(C)(z)) :=
    λ C z pZeroMap, surjective_map.mk
      (
        λ y,
        (
          exactness(C)(z)(y)(zero_map.goes_to_zero(pZeroMap)(y))
        )
      )

/-
Proof of the fact that if 0 → A → B → 0 is exact, then the map
from A to B is bijective
-/
theorem left_right_zero_implies_bijective : Π (C : ab_exact_chain_complex), Π (z : ℤ),
  zero_map(boundary_map(C)(z)) → zero_map(boundary_map(C)(z-1-1)) → bijective_map(boundary_map(C)(z-1)) :=
    λ C z pLeftZeroMap pRightZeroMap,
      surjective_and_injective_imply_bijective
      (right_zero_implies_surjective(C)(z-1)(pRightZeroMap))
      (left_zero_implies_injective(C)(z)(pLeftZeroMap))

/-
Four lemma
-/

lemma lFlLemmaOne : Π {C₁ C₂ : ab_exact_chain_complex}, Π (M : exact_chain_map (C₁) (C₂)), Π (z : ℤ),
  surjective_map (group_map(M)(z)) → surjective_map (group_map(M)(z-1-1)) → injective_map (group_map(M)(z-1-1-1)) →
  (Π (b' : chain_group(C₂)(z-1)), (Σ (c : chain_group(C₁)(z-1-1)), group_map(M)(z-1-1)(c) = boundary_map(C₂)(z-1)(b'))) :=
    λ C₁ C₂ M z proofSurj_m proofSurj_p proofInj_q b',
      ((λ c', surjective_map.get_preimage(proofSurj_p)(c'))
       (boundary_map(C₂)(z-1)(b')))

lemma lFlLemmaTwo : Π {C₁ C₂ : ab_exact_chain_complex}, Π (M : exact_chain_map (C₁) (C₂)), Π (z : ℤ),
  surjective_map (group_map(M)(z)) → surjective_map (group_map(M)(z-1-1)) → injective_map (group_map(M)(z-1-1-1)) →
  Π (c : chain_group(C₁)(z-1-1)), (boundary_map(C₂)(z-1-1)(group_map(M)(z-1-1)(c)) = group.one(chain_group(C₂)(z-1-1-1))) →
  (boundary_map(C₁)(z-1-1)(c) = group.one(chain_group(C₁)(z-1-1-1))) :=
    λ C₁ C₂ M z proofSurj_m proofSurj_p proofInj_q c proofBottomRight,
      injective_map.comes_from_zero (proofInj_q) (boundary_map(C₁)(z-1-1)(c))
      (eq.trans
        (eq.symm (commutes(M)(z-1-1)(c)))
        (proofBottomRight)
      )

lemma lFlLemmaThree : Π {C₁ C₂ : ab_exact_chain_complex}, Π (M : exact_chain_map (C₁) (C₂)), Π (z : ℤ),
  surjective_map (group_map(M)(z)) → surjective_map (group_map(M)(z-1-1)) → injective_map (group_map(M)(z-1-1-1)) →
  Π (b' : chain_group(C₂)(z-1)), Π (c : chain_group(C₁)(z-1-1)),
  ((group_map(M)(z-1-1)(c)) = (boundary_map(C₂)(z-1)(b'))) → (boundary_map(C₁)(z-1-1)(c) = group.one(chain_group(C₁)(z-1-1-1))) :=
    λ C₁ C₂ M z proofSurj_m proofSurj_p proofInj_q b' c proofEq,
    lFlLemmaTwo (M) (z) (proofSurj_m) (proofSurj_p) (proofInj_q) (c)
    (eq.trans (transport_equality_hom (boundary_map(C₂)(z-1-1)) (proofEq))
    (boundary_of_boundary(C₂)(z-1)(b')))

lemma lFlLemmaFour : Π {C₁ C₂ : ab_exact_chain_complex}, Π (M : exact_chain_map (C₁) (C₂)), Π (z : ℤ),
  surjective_map (group_map(M)(z)) → surjective_map (group_map(M)(z-1-1)) → injective_map (group_map(M)(z-1-1-1)) →
  Π (b' : chain_group(C₂)(z-1)), Σ (b : chain_group(C₁)(z-1)), (group_map(M)(z-1-1)(boundary_map(C₁)(z-1)(b)) = boundary_map(C₂)(z-1)(b')) :=
    λ C₁ C₂ M z proofSurj_m proofSurj_p proofInj_q b',
    (
    (λ c proofEq,
      sigma.mk
      (pr₁(exactness(C₁)(z-1)(c) (lFlLemmaThree (M) (z) (proofSurj_m) (proofSurj_p) (proofInj_q) (b') (c) (proofEq) )))
      (
        eq.trans  
        (transport_equality_hom (group_map(M)(z-1-1)) (pr₂(exactness(C₁)(z-1)(c) (lFlLemmaThree (M) (z) (proofSurj_m) (proofSurj_p) (proofInj_q) (b') (c) (proofEq) ))))
        (proofEq)
      )
    )
    (pr₁(lFlLemmaOne (M) (z) (proofSurj_m) (proofSurj_p) (proofInj_q) (b')))
    (pr₂(lFlLemmaOne (M) (z) (proofSurj_m) (proofSurj_p) (proofInj_q) (b')))
    )

lemma lFlLemmaFive : Π {C₁ C₂ : ab_exact_chain_complex}, Π (M : exact_chain_map (C₁) (C₂)), Π (z : ℤ),
  surjective_map (group_map(M)(z)) → surjective_map (group_map(M)(z-1-1)) → injective_map (group_map(M)(z-1-1-1)) →
  Π (b' : chain_group(C₂)(z-1)), Σ (b : chain_group(C₁)(z-1)), boundary_map(C₂)(z-1)(group_map(M)(z-1)(b)) = boundary_map(C₂)(z-1)(b') :=
    λ C₁ C₂ M z proofSurj_m proofSurj_p proofInj_q b',
    (
      (λ b proofEq,
        sigma.mk (b) (eq.trans (commutes(M)(z-1)(b)) (proofEq))
      )
      (pr₁(lFlLemmaFour (M) (z) (proofSurj_m) (proofSurj_p) (proofInj_q) (b')))
      (pr₂(lFlLemmaFour (M) (z) (proofSurj_m) (proofSurj_p) (proofInj_q) (b')))
    )

lemma lFlLemmaSix : Π {C₁ C₂ : ab_exact_chain_complex}, Π (M : exact_chain_map (C₁) (C₂)), Π (z : ℤ),
  surjective_map (group_map(M)(z)) → surjective_map (group_map(M)(z-1-1)) → injective_map (group_map(M)(z-1-1-1)) →
  Π (b' : chain_group(C₂)(z-1)), Σ (b : chain_group(C₁)(z-1)), boundary_map(C₂)(z-1)((b'⁻¹)*group_map(M)(z-1)(b)) = 1 :=
    λ C₁ C₂ M z proofSurj_m proofSurj_p proofInj_q b',
    (
      (λ b proofEq,
        sigma.mk (b) 
        (hom_respects_cancelling (boundary_map(C₂)(z-1)) (proofEq))
      )
      (pr₁(lFlLemmaFive (M) (z) (proofSurj_m) (proofSurj_p) (proofInj_q) (b')))
      (pr₂(lFlLemmaFive (M) (z) (proofSurj_m) (proofSurj_p) (proofInj_q) (b')))
    )

lemma lFlLemmaSeven : Π {C₁ C₂ : ab_exact_chain_complex}, Π (M : exact_chain_map (C₁) (C₂)), Π (z : ℤ),
  surjective_map (group_map(M)(z)) → surjective_map (group_map(M)(z-1-1)) → injective_map (group_map(M)(z-1-1-1)) →
  Π (b' : chain_group(C₂)(z-1)), Π (b : chain_group(C₁)(z-1)), boundary_map(C₂)(z-1)((b'⁻¹)*group_map(M)(z-1)(b)) = 1 → 
  Σ (a : chain_group(C₁)(z)), boundary_map(C₂)(z)(group_map(M)(z)(a)) = (b'⁻¹)*group_map(M)(z-1)(b) :=
    λ C₁ C₂ M z proofSurj_m proofSurj_p proofInj_q b' b proofZero,
    (
    (λ a' proofPreImage,
      sigma.mk
      (pr₁(surjective_map.get_preimage(proofSurj_m)(a')))
      (eq.trans
        (transport_equality_hom (boundary_map(C₂)(z)) (pr₂(surjective_map.get_preimage(proofSurj_m)(a'))))
        (proofPreImage)
      )
    )
    (pr₁(exactness(C₂)(z)((b'⁻¹)*group_map(M)(z-1)(b))(proofZero)))
    (pr₂(exactness(C₂)(z)((b'⁻¹)*group_map(M)(z-1)(b))(proofZero)))
    )

lemma lFlLemmaEight : Π {C₁ C₂ : ab_exact_chain_complex}, Π (M : exact_chain_map (C₁) (C₂)), Π (z : ℤ),
  surjective_map (group_map(M)(z)) → surjective_map (group_map(M)(z-1-1)) → injective_map (group_map(M)(z-1-1-1)) →
  Π (b' : chain_group(C₂)(z-1)), Π (b : chain_group(C₁)(z-1)), boundary_map(C₂)(z-1)((b'⁻¹)*group_map(M)(z-1)(b)) = 1 → 
  Σ (a : chain_group(C₁)(z)), group_map(M)(z-1)(boundary_map(C₁)(z)(a)) = (b'⁻¹)*group_map(M)(z-1)(b) :=
    λ C₁ C₂ M z proofSurj_m proofSurj_p proofInj_q b' b proofZero,
    (
    (λ a proofBottomRight,
    sigma.mk
    (a)
    (eq.trans (eq.symm (commutes(M)(z)(a))) (proofBottomRight))
    )
    (pr₁(lFlLemmaSeven (M) (z) (proofSurj_m) (proofSurj_p) (proofInj_q) (b') (b) (proofZero)))
    (pr₂(lFlLemmaSeven (M) (z) (proofSurj_m) (proofSurj_p) (proofInj_q) (b') (b) (proofZero)))
    )

lemma lFlLemmaNine : Π {C₁ C₂ : ab_exact_chain_complex}, Π (M : exact_chain_map (C₁) (C₂)), Π (z : ℤ),
  surjective_map (group_map(M)(z)) → surjective_map (group_map(M)(z-1-1)) → injective_map (group_map(M)(z-1-1-1)) →
  Π (b' : chain_group(C₂)(z-1)), Σ (j : chain_group(C₁)(z-1)), group_map(M)(z-1)(j) = b' :=
    λ C₁ C₂ M z proofSurj_m proofSurj_p proofInj_q b',
    (
    (λ b proofEq1,
      (λ a proofEq2,
        sigma.mk
        ((boundary_map(C₁)(z)(a))⁻¹*b)
        (eq.symm (combine_terms (group_map(M)(z-1)) (boundary_map(C₁)(z)(a)) (b) (b') (proofEq2)))
      )
      (pr₁ (lFlLemmaEight (M) (z) (proofSurj_m) (proofSurj_p) (proofInj_q) (b') (b) (proofEq1)))
      (pr₂ (lFlLemmaEight (M) (z) (proofSurj_m) (proofSurj_p) (proofInj_q) (b') (b) (proofEq1)))
    )
    (pr₁ (lFlLemmaSix (M) (z) (proofSurj_m) (proofSurj_p) (proofInj_q) (b')))
    (pr₂ (lFlLemmaSix (M) (z) (proofSurj_m) (proofSurj_p) (proofInj_q) (b')))
    )

theorem FourLemma : Π {C₁ C₂ : ab_exact_chain_complex}, Π (M : exact_chain_map (C₁) (C₂)), Π (z : ℤ),
  surjective_map (group_map(M)(z)) → surjective_map (group_map(M)(z-1-1)) → injective_map (group_map(M)(z-1-1-1)) →
  surjective_map (group_map(M)(z-1)) :=
    λ C₁ C₂ M z proofSurj_m proofSurj_p proofInj_q,
      surjective_map.mk (λ b', lFlLemmaNine (M) (z) (proofSurj_m) (proofSurj_p) (proofInj_q) (b'))
