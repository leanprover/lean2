/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Declaration of the n-spheres
-/

import .susp types.trunc

open eq nat susp bool is_trunc unit pointed algebra equiv

/-
  We can define spheres with the following possible indices:
  - trunc_index (defining S^-2 = S^-1 = empty)
  - nat (forgetting that S^-1 = empty)
  - nat, but counting wrong (S^0 = empty, S^1 = bool, ...)
  - some new type "integers >= -1"
  We choose the second option here.
-/

definition sphere (n : ℕ) : Type* := iterate_susp n pbool

namespace sphere

  namespace ops
    abbreviation S := sphere
  end ops
  open sphere.ops

  definition sphere_succ [unfold_full] (n : ℕ) : S (n+1) = susp (S n) := idp
  definition sphere_eq_iterate_susp (n : ℕ) : S n = iterate_susp n pbool := idp

  definition equator [constructor] (n : ℕ) : S n →* Ω (S (succ n)) :=
  loop_susp_unit (S n)

  definition surf {n : ℕ} : Ω[n] (S n) :=
  begin
    induction n with n s,
    { exact tt },
    { exact (loopn_succ_in (S (succ n)) n)⁻¹ᵉ* (apn n (equator n) s) }
  end

  definition sphere_equiv_bool [constructor] : S 0 ≃ bool := by reflexivity

  definition sphere_pequiv_pbool [constructor] : S 0 ≃* pbool := by reflexivity

  definition sphere_pequiv_iterate_susp (n : ℕ) : sphere n ≃* iterate_susp n pbool :=
  by reflexivity

  definition sphere_pmap_pequiv' (A : Type*) (n : ℕ) : ppmap (S n) A ≃* Ω[n] A :=
  begin
    revert A, induction n with n IH: intro A,
    { refine !ppmap_pbool_pequiv },
    { refine susp_adjoint_loop (S n) A ⬝e* IH (Ω A) ⬝e* !loopn_succ_in⁻¹ᵉ*  }
  end

  definition sphere_pmap_pequiv (A : Type*) (n : ℕ) : ppmap (S n) A ≃* Ω[n] A :=
  begin
    fapply pequiv_change_fun,
    { exact sphere_pmap_pequiv' A n },
    { exact papn_fun A surf },
    { revert A, induction n with n IH: intro A,
      { reflexivity },
      { intro f, refine ap !loopn_succ_in⁻¹ᵉ* (IH (Ω A) _ ⬝ !apn_pcompose _) ⬝ _,
        exact !loopn_succ_in_inv_natural⁻¹* _ }}
  end

  protected definition elim {n : ℕ} {P : Type*} (p : Ω[n] P) : S n →* P :=
  !sphere_pmap_pequiv⁻¹ᵉ* p

  -- definition elim_surf {n : ℕ} {P : Type*} (p : Ω[n] P) : apn n (sphere.elim p) surf = p :=
  -- begin
  --   induction n with n IH,
  --   { esimp [apn,surf,sphere.elim,sphere_pmap_equiv], apply sorry},
  --   { apply sorry}
  -- end

end sphere

namespace sphere
  open is_conn trunc_index sphere.ops

  -- Corollary 8.2.2
  theorem is_conn_sphere [instance] (n : ℕ) : is_conn (n.-1) (S n) :=
  begin
    induction n with n IH,
    { apply is_conn_minus_one_pointed },
    { apply is_conn_susp, exact IH }
  end

end sphere

open sphere sphere.ops

namespace is_trunc
  open trunc_index
  variables {n : ℕ} {A : Type}
  definition is_trunc_of_sphere_pmap_equiv_constant
    (H : Π(a : A) (f : S n →* pointed.Mk a) (x : S n), f x = f pt) : is_trunc (n.-2.+1) A :=
  begin
    apply iff.elim_right !is_trunc_iff_is_contr_loop,
    intro a,
    apply is_trunc_equiv_closed, exact !sphere_pmap_pequiv,
    fapply is_contr.mk,
    { exact pmap.mk (λx, a) idp},
    { intro f, fapply pmap_eq,
      { intro x, esimp, refine !respect_pt⁻¹ ⬝ (!H ⬝ !H⁻¹)},
      { rewrite [▸*,con.right_inv,▸*,con.left_inv]}}
  end

  definition is_trunc_iff_map_sphere_constant
    (H : Π(f : S n → A) (x : S n), f x = f pt) : is_trunc (n.-2.+1) A :=
  begin
    apply is_trunc_of_sphere_pmap_equiv_constant,
    intros, cases f with f p, esimp at *, apply H
  end

  definition sphere_pmap_equiv_constant_of_is_trunc' [H : is_trunc (n.-2.+1) A]
    (a : A) (f : S n →* pointed.Mk a) (x : S n) : f x = f pt :=
  begin
    let H' := iff.elim_left (is_trunc_iff_is_contr_loop n A) H a,
    note H'' := @is_trunc_equiv_closed_rev _ _ _ !sphere_pmap_pequiv H',
    esimp at H'',
    have p : f = pmap.mk (λx, f pt) (respect_pt f),
      by apply is_prop.elim,
    exact ap10 (ap pmap.to_fun p) x
  end

  definition sphere_pmap_equiv_constant_of_is_trunc [H : is_trunc (n.-2.+1) A]
    (a : A) (f : S n →* pointed.Mk a) (x y : S n) : f x = f y :=
  let H := sphere_pmap_equiv_constant_of_is_trunc' a f in !H ⬝ !H⁻¹

  definition map_sphere_constant_of_is_trunc [H : is_trunc (n.-2.+1) A]
    (f : S n → A) (x y : S n) : f x = f y :=
  sphere_pmap_equiv_constant_of_is_trunc (f pt) (pmap.mk f idp) x y

  definition map_sphere_constant_of_is_trunc_self [H : is_trunc (n.-2.+1) A]
    (f : S n → A) (x : S n) : map_sphere_constant_of_is_trunc f x x = idp :=
  !con.right_inv

end is_trunc
