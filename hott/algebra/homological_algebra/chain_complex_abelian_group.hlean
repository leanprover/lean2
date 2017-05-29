/-
Copyright (c) 2017 Sayantan Khan
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sayantan Khan

Structures for chain complexes. Currently only supports abelian groups.
-/

import algebra.group_theory 
import types.int

open algebra
open int
open group

namespace abelian_chain_complex

structure zero_map {G₁ G₂ : AbGroup} (φ : homomorphism (G₁) (G₂)) : Type :=
  (goes_to_zero : Π (x : G₁), φ(x) = group.one(G₂))
  
structure surjective_map {G₁ G₂ : AbGroup} (φ : homomorphism (G₁) (G₂)) : Type :=
  (get_preimage : Π (y : G₂), Σ (x : G₁), φ(x) = y)
  
structure injective_map {G₁ G₂ : AbGroup} (φ : homomorphism (G₁) (G₂)) : Type :=
  (comes_from_zero : Π (x : G₁), (φ(x) = group.one(G₂)) → (x = group.one(G₁)))

structure bijective_map {G₁ G₂ : AbGroup} (φ : homomorphism (G₁) (G₂)) : Type :=
  (get_preimage : Π (y : G₂), Σ (x : G₁), φ(x) = y)
  (comes_from_zero : Π (x : G₁), (φ(x) = group.one(G₂)) → (x = group.one(G₁)))
  
structure ab_chain_complex : Type :=
  (chain_group  : ℤ → AbGroup)
  (boundary_map : Π (z : ℤ), homomorphism (chain_group(z)) (chain_group(z-1)))
  (boundary_of_boundary : Π (z : ℤ), Π (c : chain_group(z)), boundary_map(z-1)(boundary_map(z)(c)) = group.one(chain_group(z-1-1)))
  
structure chain_map (C₁ C₂ : ab_chain_complex) : Type :=
  (group_map : Π (z : ℤ), homomorphism (ab_chain_complex.chain_group(C₁)(z)) (ab_chain_complex.chain_group(C₂)(z)))
  (commutes : Π (z : ℤ), Π (c : ab_chain_complex.chain_group(C₁)(z)),
    (ab_chain_complex.boundary_map (C₂) (z) (group_map (z) (c))) 
  = (group_map (z-1) (ab_chain_complex.boundary_map (C₁) (z) (c))))

structure ab_exact_chain_complex : Type :=
  (chain_group  : ℤ → AbGroup)
  (boundary_map : Π (z : ℤ), homomorphism (chain_group(z)) (chain_group(z-1)))
  (boundary_of_boundary : Π (z : ℤ), Π (c : chain_group(z)), boundary_map(z-1)(boundary_map(z)(c)) = group.one(chain_group(z-1-1)))
  (exactness : Π (z : ℤ), Π (x : chain_group(z-1)), 
    (group_fun(boundary_map(z-1))(x) = group.one(chain_group(z-1-1))) → (Σ (y : chain_group(z)), group_fun(boundary_map(z))(y) = x))

structure exact_chain_map (C₁ C₂ : ab_exact_chain_complex) : Type :=
  (group_map : Π (z : ℤ), homomorphism (ab_exact_chain_complex.chain_group(C₁)(z)) (ab_exact_chain_complex.chain_group(C₂)(z)))
  (commutes : Π (z : ℤ), Π (c : ab_exact_chain_complex.chain_group(C₁)(z)),
    (ab_exact_chain_complex.boundary_map (C₂) (z) (group_map (z) (c)))
  = (group_map (z-1) (ab_exact_chain_complex.boundary_map (C₁) (z) (c))))

end abelian_chain_complex
