import ..group_theory 
import types.int

open algebra
open int
open group

namespace abelian_chain_complex

structure zero_map {G₁ G₂ : AbGroup} (φ : homomorphism (G₁) (G₂)) : Type :=
  (goes_to_zero : Π (x : G₁), group_fun(φ)(x) = group.one(G₂))
  
structure surjective_map {G₁ G₂ : AbGroup} (φ : homomorphism (G₁) (G₂)) : Type :=
  (get_preimage : Π (y : G₂), Σ (x : G₁), group_fun(φ)(x) = y)
  
structure injective_map {G₁ G₂ : AbGroup} (φ : homomorphism (G₁) (G₂)) : Type :=
  (comes_from_zero : Π (x : G₁), (group_fun(φ)(x) = group.one(G₂)) → (x = group.one(G₁)))
  
structure ab_chain_complex : Type :=
  (chain_group  : ℤ → AbGroup)
  (boundary_map : Π (z : ℤ), homomorphism (chain_group(z)) (chain_group(z-1)))
  (boundary_of_boundary : Π (z : ℤ), zero_map (homomorphism_compose (boundary_map(z-1)) (boundary_map(z))))
  
structure ab_exact_chain_complex : Type :=
  (chain_group  : ℤ → AbGroup)
  (boundary_map : Π (z : ℤ), homomorphism (chain_group(z)) (chain_group(z-1)))
  (boundary_of_boundary : Π (z : ℤ), zero_map (homomorphism_compose (boundary_map(z-1)) (boundary_map(z))))
  (exactness : Π (z : ℤ), Π (x : chain_group(z-1)), 
    (group_fun(boundary_map(z-1))(x) = group.one(chain_group(z-1-1))) → (Σ (y : chain_group(z)), group_fun(boundary_map(z))(y) = x))

open ab_exact_chain_complex

check @injective_map.mk

-- lemma left_zero_implies_injective : Π (C : ab_exact_chain_complex), Π (z : ℤ),
  -- zero_map(boundary_map(C)(z)) → injective_map(boundary_map(C)(z-1)) :=
    -- λ C z pZeroMap, injective_map.mk 
      -- (λ x pGoesZero)

end abelian_chain_complex
