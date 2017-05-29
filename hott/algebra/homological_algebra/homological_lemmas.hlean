/-
Copyright (c) 2017 Sayantan Khan
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sayantan Khan

Proofs of elementary homological lemmas.
-/

import algebra.group_theory
import .chain_complex_abelian_group
import .algebraic_lemmas

open int
open sigma.ops
open algebra
open group
open abelian_chain_complex
open abelian_chain_complex.ab_exact_chain_complex
open abelian_chain_complex.exact_chain_map

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
Proof of the Four Lemma. Proving the lemma requires nine lemmas,
roughly one for each step in the diagram chase. This could have
been done in a cleaner manner.
-/

lemma subLemmaOne : Π {C₁ C₂ : ab_exact_chain_complex}, Π (M : exact_chain_map (C₁) (C₂)), Π (z : ℤ),
  surjective_map (group_map(M)(z)) → surjective_map (group_map(M)(z-1-1)) → injective_map (group_map(M)(z-1-1-1)) →
  (Π (b' : chain_group(C₂)(z-1)), (Σ (c : chain_group(C₁)(z-1-1)), group_map(M)(z-1-1)(c) = boundary_map(C₂)(z-1)(b'))) :=
    λ C₁ C₂ M z proofSurj_m proofSurj_p proofInj_q b',
      ((λ c', surjective_map.get_preimage(proofSurj_p)(c'))
       (boundary_map(C₂)(z-1)(b')))

lemma subLemmaTwo : Π {C₁ C₂ : ab_exact_chain_complex}, Π (M : exact_chain_map (C₁) (C₂)), Π (z : ℤ),
  surjective_map (group_map(M)(z)) → surjective_map (group_map(M)(z-1-1)) → injective_map (group_map(M)(z-1-1-1)) →
  Π (c : chain_group(C₁)(z-1-1)), (boundary_map(C₂)(z-1-1)(group_map(M)(z-1-1)(c)) = group.one(chain_group(C₂)(z-1-1-1))) →
  (boundary_map(C₁)(z-1-1)(c) = group.one(chain_group(C₁)(z-1-1-1))) :=
    λ C₁ C₂ M z proofSurj_m proofSurj_p proofInj_q c proofBottomRight,
      injective_map.comes_from_zero (proofInj_q) (boundary_map(C₁)(z-1-1)(c))
      (eq.trans
        (eq.symm (commutes(M)(z-1-1)(c)))
        (proofBottomRight)
      )

lemma subLemmaThree : Π {C₁ C₂ : ab_exact_chain_complex}, Π (M : exact_chain_map (C₁) (C₂)), Π (z : ℤ),
  surjective_map (group_map(M)(z)) → surjective_map (group_map(M)(z-1-1)) → injective_map (group_map(M)(z-1-1-1)) →
  Π (b' : chain_group(C₂)(z-1)), Π (c : chain_group(C₁)(z-1-1)),
  ((group_map(M)(z-1-1)(c)) = (boundary_map(C₂)(z-1)(b'))) → (boundary_map(C₁)(z-1-1)(c) = group.one(chain_group(C₁)(z-1-1-1))) :=
    λ C₁ C₂ M z proofSurj_m proofSurj_p proofInj_q b' c proofEq,
    subLemmaTwo (M) (z) (proofSurj_m) (proofSurj_p) (proofInj_q) (c)
    (eq.trans (transport_equality_hom (boundary_map(C₂)(z-1-1)) (proofEq))
    (boundary_of_boundary(C₂)(z-1)(b')))

lemma subLemmaFour : Π {C₁ C₂ : ab_exact_chain_complex}, Π (M : exact_chain_map (C₁) (C₂)), Π (z : ℤ),
  surjective_map (group_map(M)(z)) → surjective_map (group_map(M)(z-1-1)) → injective_map (group_map(M)(z-1-1-1)) →
  Π (b' : chain_group(C₂)(z-1)), Σ (b : chain_group(C₁)(z-1)), (group_map(M)(z-1-1)(boundary_map(C₁)(z-1)(b)) = boundary_map(C₂)(z-1)(b')) :=
    λ C₁ C₂ M z proofSurj_m proofSurj_p proofInj_q b',
    (
    (λ c proofEq,
      sigma.mk
      (pr₁(exactness(C₁)(z-1)(c) (subLemmaThree (M) (z) (proofSurj_m) (proofSurj_p) (proofInj_q) (b') (c) (proofEq) )))
      (
        eq.trans  
        (transport_equality_hom (group_map(M)(z-1-1)) (pr₂(exactness(C₁)(z-1)(c) (subLemmaThree (M) (z) (proofSurj_m) (proofSurj_p) (proofInj_q) (b') (c) (proofEq) ))))
        (proofEq)
      )
    )
    (pr₁(subLemmaOne (M) (z) (proofSurj_m) (proofSurj_p) (proofInj_q) (b')))
    (pr₂(subLemmaOne (M) (z) (proofSurj_m) (proofSurj_p) (proofInj_q) (b')))
    )

lemma subLemmaFive : Π {C₁ C₂ : ab_exact_chain_complex}, Π (M : exact_chain_map (C₁) (C₂)), Π (z : ℤ),
  surjective_map (group_map(M)(z)) → surjective_map (group_map(M)(z-1-1)) → injective_map (group_map(M)(z-1-1-1)) →
  Π (b' : chain_group(C₂)(z-1)), Σ (b : chain_group(C₁)(z-1)), boundary_map(C₂)(z-1)(group_map(M)(z-1)(b)) = boundary_map(C₂)(z-1)(b') :=
    λ C₁ C₂ M z proofSurj_m proofSurj_p proofInj_q b',
    (
      (λ b proofEq,
        sigma.mk (b) (eq.trans (commutes(M)(z-1)(b)) (proofEq))
      )
      (pr₁(subLemmaFour (M) (z) (proofSurj_m) (proofSurj_p) (proofInj_q) (b')))
      (pr₂(subLemmaFour (M) (z) (proofSurj_m) (proofSurj_p) (proofInj_q) (b')))
    )

lemma subLemmaSix : Π {C₁ C₂ : ab_exact_chain_complex}, Π (M : exact_chain_map (C₁) (C₂)), Π (z : ℤ),
  surjective_map (group_map(M)(z)) → surjective_map (group_map(M)(z-1-1)) → injective_map (group_map(M)(z-1-1-1)) →
  Π (b' : chain_group(C₂)(z-1)), Σ (b : chain_group(C₁)(z-1)), boundary_map(C₂)(z-1)((b'⁻¹)*group_map(M)(z-1)(b)) = 1 :=
    λ C₁ C₂ M z proofSurj_m proofSurj_p proofInj_q b',
    (
      (λ b proofEq,
        sigma.mk (b) 
        (hom_respects_cancelling (boundary_map(C₂)(z-1)) (proofEq))
      )
      (pr₁(subLemmaFive (M) (z) (proofSurj_m) (proofSurj_p) (proofInj_q) (b')))
      (pr₂(subLemmaFive (M) (z) (proofSurj_m) (proofSurj_p) (proofInj_q) (b')))
    )

lemma subLemmaSeven : Π {C₁ C₂ : ab_exact_chain_complex}, Π (M : exact_chain_map (C₁) (C₂)), Π (z : ℤ),
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

lemma subLemmaEight : Π {C₁ C₂ : ab_exact_chain_complex}, Π (M : exact_chain_map (C₁) (C₂)), Π (z : ℤ),
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
    (pr₁(subLemmaSeven (M) (z) (proofSurj_m) (proofSurj_p) (proofInj_q) (b') (b) (proofZero)))
    (pr₂(subLemmaSeven (M) (z) (proofSurj_m) (proofSurj_p) (proofInj_q) (b') (b) (proofZero)))
    )

lemma subLemmaNine : Π {C₁ C₂ : ab_exact_chain_complex}, Π (M : exact_chain_map (C₁) (C₂)), Π (z : ℤ),
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
      (pr₁ (subLemmaEight (M) (z) (proofSurj_m) (proofSurj_p) (proofInj_q) (b') (b) (proofEq1)))
      (pr₂ (subLemmaEight (M) (z) (proofSurj_m) (proofSurj_p) (proofInj_q) (b') (b) (proofEq1)))
    )
    (pr₁ (subLemmaSix (M) (z) (proofSurj_m) (proofSurj_p) (proofInj_q) (b')))
    (pr₂ (subLemmaSix (M) (z) (proofSurj_m) (proofSurj_p) (proofInj_q) (b')))
    )

/-
This is the surjective variant of the Four Lemma. Proving the injective variant
of the Four Lemma will take a similar approach, and once we have both, the Five
Lemma is an easy consequence.
-/
theorem FourLemma : Π {C₁ C₂ : ab_exact_chain_complex}, Π (M : exact_chain_map (C₁) (C₂)), Π (z : ℤ),
  surjective_map (group_map(M)(z)) → surjective_map (group_map(M)(z-1-1)) → injective_map (group_map(M)(z-1-1-1)) →
  surjective_map (group_map(M)(z-1)) :=
    λ C₁ C₂ M z proofSurj_m proofSurj_p proofInj_q,
      surjective_map.mk (λ b', subLemmaNine (M) (z) (proofSurj_m) (proofSurj_p) (proofInj_q) (b'))
