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

namespace ESaxioms

open Type_ab_functor

definition cohomology := Π (z : ℤ), Type_ab_functor

definition susp_iso (H : cohomology) := 
  λ H, Π (z : ℤ), Π (X : Type*), Σ (f : fun_ty(H(z+1))(red_susp(X)) → fun_ty(H(z))(X)),
    @is_add_hom(_)(_)
    (lemmas.group_has_add(target_ab(H(z+1))(red_susp(X))))
    (lemmas.group_has_add(target_ab(H(z))(X)))
    (f)

end ESaxioms
