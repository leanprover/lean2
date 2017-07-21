/-
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

The definition of pointed types. This file is here to avoid circularities in the import graph
-/

prelude
import init.trunc

open eq equiv is_equiv is_trunc

structure pointed [class] (A : Type) :=
  (point : A)

structure pType :=
  (carrier : Type)
  (Point   : carrier)

notation `Type*` := pType

namespace pointed
  attribute pType.carrier [coercion]
  variables {A : Type}

  definition pt [reducible] [unfold 2] [H : pointed A] := point A
  definition Point [reducible] [unfold 1] (A : Type*) := pType.Point A
  definition carrier [reducible] [unfold 1] (A : Type*) := pType.carrier A
  protected definition Mk [constructor] {A : Type} (a : A) := pType.mk A a
  protected definition MK [constructor] (A : Type) (a : A) := pType.mk A a
  protected definition mk' [constructor] (A : Type) [H : pointed A] : Type* :=
  pType.mk A (point A)
  definition pointed_carrier [instance] [constructor] (A : Type*) : pointed A :=
  pointed.mk (Point A)

end pointed
open pointed

section
  universe variable u
  structure ptrunctype (n : ℕ₋₂) extends trunctype.{u} n, pType.{u}

  definition is_trunc_ptrunctype [instance] {n : ℕ₋₂} (X : ptrunctype n)
    : is_trunc n (ptrunctype.to_pType X) :=
  trunctype.struct X

end

notation n `-Type*` := ptrunctype n
abbreviation pSet  [parsing_only] := 0-Type*
notation `Set*` := pSet

namespace pointed

  protected definition ptrunctype.mk' [constructor] (n : ℕ₋₂)
    (A : Type) [pointed A] [is_trunc n A] : n-Type* :=
  ptrunctype.mk A _ pt

  protected definition pSet.mk [constructor] := @ptrunctype.mk (-1.+1)
  protected definition pSet.mk' [constructor] := ptrunctype.mk' (-1.+1)

  definition ptrunctype_of_trunctype [constructor] {n : ℕ₋₂} (A : n-Type) (a : A)
    : n-Type* :=
  ptrunctype.mk A _ a

  definition ptrunctype_of_pType [constructor] {n : ℕ₋₂} (A : Type*) (H : is_trunc n A)
    : n-Type* :=
  ptrunctype.mk A _ pt

  definition pSet_of_Set [constructor] (A : Set) (a : A) : Set* :=
  ptrunctype.mk A _ a

  definition pSet_of_pType [constructor] (A : Type*) (H : is_set A) : Set* :=
  ptrunctype.mk A _ pt

  attribute ptrunctype._trans_of_to_pType ptrunctype.to_pType ptrunctype.to_trunctype [unfold 2]

  -- Any contractible type is pointed
  definition pointed_of_is_contr [instance] [priority 800] [constructor]
    (A : Type) [H : is_contr A] : pointed A :=
  pointed.mk !center

end pointed

/- pointed maps -/
structure ppi {A : Type*} (P : A → Type) (x₀ : P pt) :=
  (to_fun : Π a : A, P a)
  (resp_pt : to_fun (Point A) = x₀)

definition ppi_const [constructor] {A : Type*} (P : A → Type*) : ppi P pt :=
ppi.mk (λa, pt) idp

definition pppi' [reducible] {A : Type*} (P : A → Type*) : Type :=
ppi P pt

definition pppi [constructor] [reducible] {A : Type*} (P : A → Type*) : Type* :=
pointed.MK (pppi' P) (ppi_const P)

notation `Π*` binders `, ` r:(scoped P, pppi P) := r

-- We could try to define pmap as a special case of ppi
-- definition pmap' (A B : Type*) : Type := @pppi' A (λa, B)
-- todo: make this already pointed?
definition pmap [reducible] (A B : Type*) : Type := @pppi A (λa, B)
-- structure pmap (A B : Type*) :=
--   (to_fun : A → B)
--   (resp_pt : to_fun (Point A) = Point B)

namespace pointed

  attribute ppi.to_fun [coercion]

  notation `map₊` := pmap
  infix ` →* `:28 := pmap

  definition pppi.mk [constructor] [reducible] {A : Type*} {P : A → Type*} (f : Πa, P a)
    (p : f pt = pt) : pppi P :=
  ppi.mk f p

  definition pppi.to_fun [unfold 3] [coercion] [reducible] {A : Type*} {P : A → Type*} (f : pppi' P)
    (a : A) : P a :=
  ppi.to_fun f a

	definition pmap.mk [constructor] [reducible] {A B : Type*} (f : A → B)
    (p : f (Point A) = Point B) : A →* B :=
	pppi.mk f p

  definition pmap.to_fun [unfold 3] [reducible] {A B : Type*} (f : A →* B) : A → B :=
  pppi.to_fun f

  definition respect_pt [unfold 4] [reducible] {A : Type*} {P : A → Type} {p₀ : P pt}
    (f : ppi P p₀) : f pt = p₀ :=
  ppi.resp_pt f

  -- notation `Π*` binders `, ` r:(scoped P, ppi _ P) := r
  -- definition pmxap.mk [constructor] {A B : Type*} (f : A → B) (p : f pt = pt) : A →* B :=
  -- ppi.mk f p
  -- definition pmap.to_fun [coercion] [unfold 3] {A B : Type*} (f : A →* B) : A → B := f

end pointed open pointed

/- pointed homotopies -/
definition phomotopy {A : Type*} {P : A → Type} {p₀ : P pt} (f g : ppi P p₀) : Type :=
ppi (λa, f a = g a) (respect_pt f ⬝ (respect_pt g)⁻¹)

-- structure phomotopy {A B : Type*} (f g : A →* B) : Type :=
--   (homotopy : f ~ g)
--   (homotopy_pt : homotopy pt ⬝ respect_pt g = respect_pt f)

namespace pointed
  variables {A : Type*} {P : A → Type} {p₀ : P pt} {f g : ppi P p₀}

  infix ` ~* `:50 := phomotopy
  definition phomotopy.mk [reducible] [constructor] (h : f ~ g)
    (p : h pt ⬝ respect_pt g = respect_pt f) : f ~* g :=
  ppi.mk h (eq_con_inv_of_con_eq p)

  definition to_homotopy [coercion] [unfold 5] [reducible] (p : f ~* g) : Πa, f a = g a := p
  definition to_homotopy_pt [unfold 5] [reducible] (p : f ~* g) :
    p pt ⬝ respect_pt g = respect_pt f :=
  con_eq_of_eq_con_inv (respect_pt p)


end pointed
