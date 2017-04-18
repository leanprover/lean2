/-
Authors : Sayantan Khan

Formalizing (generalized) cohomology theory using Eilenberg-Steenrod axioms.
-/

import .type_ab_functor
import types.int homotopy.red_susp types.pointed
import algebra.group algebra.homomorphism

open pointed
open red_susp
open int
open algebra

namespace lemmas

lemma group_has_add : Π {A : Type}, add_ab_group(A) → has_add(A) := _

end lemmas

namespace aux_definitions

structure abelian_isomorphism (G₁ G₂ : Type) : Type :=
  (φ : G₁ → G₂)
  (proofG₁ : add_ab_group(G₁))
  (proofG₂ : add_ab_group(G₂))
  (p : is_add_hom φ)
  (iso_is_equiv : is_equiv φ)

axiom induced_map : Π {X Y : Type*}, Π (f : X →* Y), red_susp(X) →* red_susp(Y)

end aux_definitions

namespace ESaxioms

open Type_ab_functor
open aux_definitions

definition cohomology := Π (z : ℤ), Type_ab_functor

definition susp_iso' (H : cohomology) := 
  λ H, Π (z : ℤ), Π (X : Type*), abelian_isomorphism (fun_ty (H(z+1)) (red_susp(X))) (fun_ty (H(z)) (X))
  
structure suspension (H : cohomology) : Type :=
  (susp_iso : Π (z : ℤ), Π (X : Type*),
    abelian_isomorphism (fun_ty (H(z+1)) (red_susp(X))) (fun_ty (H(z)) (X)))
  -- (naturality : Π (z : ℤ), Π (X Y : Type*), Π (f : X →* Y),
  --   (() ∘ ())
  --   =
  --   ())
    

-- definition naturality_susp_iso : Π (H : cohomology), susp_iso(H) → Type := ℕ
variable H : cohomology
variable susp : suspension(H)
check suspension.susp_iso(susp)
check unit

end ESaxioms
