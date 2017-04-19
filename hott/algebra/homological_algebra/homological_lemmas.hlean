/-
Copyright (c) 2017 Sayantan Khan
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sayantan Khan

Proofs of elementary lemmas.
-/

import .chain_complex_abelian_group

open int
open sigma.ops
open abelian_chain_complex
open abelian_chain_complex.ab_exact_chain_complex

/-
Proof of the the fact the if 0 → A → B is exact, then the map
from A to B is injective.
-/
lemma left_zero_implies_injective : Π (C : ab_exact_chain_complex), Π (z : ℤ),
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
lemma right_zero_implies_surjective : Π (C : ab_exact_chain_complex), Π (z : ℤ),
  zero_map(boundary_map(C)(z-1)) → surjective_map(boundary_map(C)(z)) :=
    λ C z pZeroMap, surjective_map.mk
      (
        λ y,
        (
          exactness(C)(z)(y)(zero_map.goes_to_zero(pZeroMap)(y))
        )
      )
