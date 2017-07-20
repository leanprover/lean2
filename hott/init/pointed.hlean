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
structure ppi_gen {A : Type*} (P : A → Type) (x₀ : P pt) :=
  (to_fun : Π a : A, P a)
  (resp_pt : to_fun (Point A) = x₀)

definition ppi {A : Type*} (P : A → Type*) : Type :=
ppi_gen P pt

-- We could try to define pmap as a special case of ppi
-- definition pmap (A B : Type*) := @ppi A (λa, B)
structure pmap (A B : Type*) :=
  (to_fun : A → B)
  (resp_pt : to_fun (Point A) = Point B)

namespace pointed
  definition ppi.mk [constructor] [reducible] {A : Type*} {P : A → Type*} (f : Πa, P a)
    (p : f pt = pt) : ppi P :=
  ppi_gen.mk f p

  definition ppi.to_fun [unfold 3] [coercion] [reducible] {A : Type*} {P : A → Type*} (f : ppi P)
    (a : A) : P a :=
  ppi_gen.to_fun f a

  definition ppi.resp_pt [unfold 3] [reducible] {A : Type*} {P : A → Type*} (f : ppi P) :
    f pt = pt :=
  ppi_gen.resp_pt f

  abbreviation respect_pt [unfold 3] := @pmap.resp_pt
  notation `map₊` := pmap
  infix ` →* `:28 := pmap
  attribute pmap.to_fun ppi_gen.to_fun [coercion]
  -- notation `Π*` binders `, ` r:(scoped P, ppi _ P) := r
  -- definition pmap.mk [constructor] {A B : Type*} (f : A → B) (p : f pt = pt) : A →* B :=
  -- ppi.mk f p
  -- definition pmap.to_fun [coercion] [unfold 3] {A B : Type*} (f : A →* B) : A → B := f

end pointed open pointed

/- pointed homotopies -/
definition phomotopy {A B : Type*} (f g : A →* B) : Type :=
ppi_gen (λa, f a = g a) (respect_pt f ⬝ (respect_pt g)⁻¹)

-- structure phomotopy {A B : Type*} (f g : A →* B) : Type :=
--   (homotopy : f ~ g)
--   (homotopy_pt : homotopy pt ⬝ respect_pt g = respect_pt f)

namespace pointed
  variables {A B : Type*} {f g : A →* B}

  infix ` ~* `:50 := phomotopy
  definition phomotopy.mk [reducible] [constructor] (h : f ~ g)
    (p : h pt ⬝ respect_pt g = respect_pt f) : f ~* g :=
  ppi_gen.mk h (eq_con_inv_of_con_eq p)

  definition to_homotopy [coercion] [unfold 5] [reducible] (p : f ~* g) : Πa, f a = g a := p
  definition to_homotopy_pt [unfold 5] [reducible] (p : f ~* g) :
    p pt ⬝ respect_pt g = respect_pt f :=
  con_eq_of_eq_con_inv (ppi_gen.resp_pt p)


end pointed
