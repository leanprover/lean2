/-
Authors: Sayantan Khan

Contravariant functors from (pointed?) Types to Abelian groups.
-/

import algebra.group algebra.homomorphism
import types.pointed

open algebra
open sigma.ops
open function
open pointed

structure type_ab_functor : Type :=
  (fun_ty : Type → Type)
  (target_ab : Π (A), add_ab_group(fun_ty(A)))
  (fun_arr : Π {A B}, (A → B) → (Σ (f : fun_ty(B) → fun_ty(A)), is_add_hom(f)))
  (respect_id : Π {A}, pr₁(fun_arr (@id A)) = id)
  (respect_comp : Π {A B C}, Π (f : A → B), Π (g : B → C),
    (pr₁(fun_arr (g ∘ f))) = ((pr₁ (fun_arr(f))) ∘ (pr₁ (fun_arr(g)))))

attribute [coercion] type_ab_functor.fun_ty

lemma extract_add : Π (A : Type), ab_group(A) → has_add(A) :=
  λ A proofOfAbGroup, has_add.mk(algebra.ab_group.mul)

structure Type_ab_functor : Type :=
  (fun_ty : Type* → Type)
  (target_ab : Π (A), add_ab_group(fun_ty(A)))
  (fun_arr : Π {A B : Type*}, (A →* B) → (Σ (f : fun_ty(B) → fun_ty(A)), is_add_hom(f)))
  (respect_id : Π {A}, pr₁(fun_arr (pid A)) = id)
  (respect_comp : Π {A B C}, Π (f : A →* B), Π (g : B →* C),
    (pr₁(fun_arr (g ∘* f))) = ((pr₁ (fun_arr(f))) ∘ (pr₁ (fun_arr(g)))))

attribute [coercion] Type_ab_functor.fun_ty
