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

/-
Auxiliary lemmas. May be moved somewhere else.
-/

lemma transport_equality : Π {G₁ G₂ : AbGroup}, Π (φ : homomorphism (G₁) (G₂)), Π {x y : G₁},
  (x = y) → (φ(x) = φ(y)) :=
    λ G₁ G₂ φ x, @eq.rec(_)(x)(_) (eq.refl(group_fun φ(x)))

lemma hom_respects_one : Π {G₁ G₂ : AbGroup}, Π (φ : homomorphism (G₁) (G₂)), Π (x : G₁),
  (x = group.one(G₁)) → (φ(x) = group.one(G₂)) :=
    λ G₁ G₂ φ x proofOfOne, eq.trans (transport_equality (φ)(proofOfOne)) (respect_one φ)

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
    (eq.trans (transport_equality (boundary_map(C₂)(z-1-1)) (proofEq))
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
        (transport_equality (group_map(M)(z-1-1)) (pr₂(exactness(C₁)(z-1)(c) (lFlLemmaThree (M) (z) (proofSurj_m) (proofSurj_p) (proofInj_q) (b') (c) (proofEq) ))))
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
-- lemma lFlLemmaThree : Π {C₁ C₂ : ab_exact_chain_complex}, Π (M : exact_chain_map (C₁) (C₂)), Π (z : ℤ),
--   surjective_map (group_map(M)(z)) → surjective_map (group_map(M)(z-1-1)) → injective_map (group_map(M)(z-1-1-1)) →
--   (Π (b' : chain_group(C₂)(z-1)), (Σ (b : chain_group(C₁)(z-1)), boundary_map(C₂)(z-1)(b') = boundary_map(C₂)(z-1)(group_map(M)(z-1)(b)))) :=
--     λ C₁ C₂ M z proofSurj_m proofSurj_p proofInj_q b',
--     (
--     (λ c proofcGoesZero,
--       sigma.mk
--       (sorry)
--       (sorry)
--     )
--     (pr₁(lFlLemmaOne (M) (z) (proofSurj_m) (proofSurj_p) (proofInj_q) (b')))
--     ( 
--       lFlLemmaTwo (M) (z) (proofSurj_m) (proofSurj_p) (proofInj_q) (pr₁(lFlLemmaOne (M) (z) (proofSurj_m) (proofSurj_p) (proofInj_q) (b')))
--       (eq.trans
--         (eq.symm (commutes (M) (z-1-1) (pr₁(lFlLemmaOne (M) (z) (proofSurj_m) (proofSurj_p) (proofInj_q) (b')))))
--         (transport_equality (boundary_map(C₂)(z-1-1)) (pr₂(lFlLemmaOne (M) (z) (proofSurj_m) (proofSurj_p) (proofInj_q) (b'))))
--       )
--     )
--     )
