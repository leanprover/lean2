/-
Copyright (c) 2015 Joe Hendrix. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joe Hendrix

Basic operations on bitvectors.

This is a work-in-progress, and contains additions to other theories.
-/
import data.list
import data.tuple

namespace bv
open bool
open eq.ops
open list
open nat
open prod
open subtype
open tuple

definition bv [reducible] (n : ℕ) := tuple bool n

-- Create a zero bitvector
definition bv_zero (n : ℕ) : bv n := replicate n ff

-- Create  a bitvector with the constant one.
definition bv_one  : Π (n : ℕ), bv n
  | 0 := nil
  | (succ n) := (replicate n ff : bv n) ++ (tt :: nil)

definition bv_cong {a b : ℕ} : (a = b) → bv a → bv b
| c (tag x p) := tag x (c ▸ p)

section shift

  -- shift left
  definition bv_shl {n:ℕ} : bv n → ℕ → bv n
    | x i :=
       if le : i ≤ n then
         let r := dropn i x ++ replicate i ff in
         let eq := calc (n-i) + i = n : nat.sub_add_cancel le in
         bv_cong eq r
       else
         bv_zero n

  definition fill_shr {n:ℕ} (x : bv n) (i : ℕ) (fill : bool) : bv n :=
  let y := replicate (min n i) fill ++ firstn (n-i) x in
  have min n i + min (n-i) n = n, from if h : i ≤ n then
    by rewrite [min_eq_right h, min_eq_left !sub_le, -nat.add_sub_assoc h,
      nat.add_sub_cancel_left]
  else
    have h : i ≥ n, from le_of_not_ge h,
    by rewrite [min_eq_left h, sub_eq_zero_of_le h, min_eq_left !zero_le],
  bv_cong this y

 -- unsigned shift right
  definition bv_ushr {n:ℕ} : bv n → ℕ → bv n
    | x i :=
  fill_shr x i ff

  -- signed shift right
  definition bv_sshr {m:ℕ} : bv (succ m) → ℕ → bv (succ m)
    | x i := head x :: fill_shr (tail x) i (head x)
end shift

section bitwise
  variable { n : ℕ }

  definition bv_not : bv n → bv n := map bnot
  definition bv_and : bv n → bv n → bv n := map₂ band
  definition bv_or  : bv n → bv n → bv n := map₂ bor
  definition bv_xor : bv n → bv n → bv n := map₂ bxor

end bitwise

section arith

  variable { n : ℕ }

  protected definition xor3 (x:bool) (y:bool) (c:bool) := bxor (bxor x y) c
  protected definition carry (x:bool) (y:bool) (c:bool) :=
    x && y || x && c || y && c

  definition bv_neg : bv n → bv n
  | x :=
    let f := λy c, (y || c, bxor y c) in
    pr₂ (mapAccumR f x ff)

  -- Add with carry (no overflow)
  definition bv_adc : bv n → bv n → bool → bv (n+1)
  | x y c :=
    let f := λx y c, (bv.carry x y c, bv.xor3 x y c) in
    let z := tuple.mapAccumR₂ f x y c in
    (pr₁ z) :: (pr₂ z)

  definition bv_add : bv n → bv n → bv n
  | x y := tail (bv_adc x y ff)

  protected definition borrow (x:bool) (y:bool) (b:bool) :=
    bnot x && y || bnot x && b || y && b

  -- Subtract with borrow
  definition bv_sbb : bv n → bv n → bool → bool × bv n
  | x y b :=
    let f := λx y c, (bv.borrow x y c, bv.xor3 x y c) in
    tuple.mapAccumR₂ f x y b

  definition bv_sub : bv n → bv n → bv n
  | x y := pr₂ (bv_sbb x y ff)

  definition bv_has_zero [instance] : has_zero (bv n) := has_zero.mk (bv_zero n)
  definition bv_has_one  [instance] : has_one (bv n)  := has_one.mk (bv_one n)
  definition bv_has_add  [instance] : has_add (bv n)  := has_add.mk bv_add
  definition bv_has_sub  [instance] : has_sub (bv n)  := has_sub.mk bv_sub
  definition bv_has_neg  [instance] : has_neg (bv n)  := has_neg.mk bv_neg

  definition bv_mul : bv n → bv n → bv n
  | x y :=
    let f := λr b, cond b (r + r + y) (r + r) in
    foldl f 0 (to_list x)

  definition bv_has_mul  [instance] : has_mul (bv n)  := has_mul.mk bv_mul

  definition bv_ult : bv n → bv n → bool := λx y, pr₁ (bv_sbb x y ff)
  definition bv_ugt : bv n → bv n → bool := λx y, bv_ult y x
  definition bv_ule : bv n → bv n → bool := λx y, bnot (bv_ult y x)
  definition bv_uge : bv n → bv n → bool := λx y, bv_ule y x

  definition bv_slt : bv (succ n) → bv (succ n) → bool := λx y,
    cond (head x)
         (cond (head y)
               (bv_ult (tail x) (tail y))  -- both negative
               tt)                         -- x is negative and y is not
         (cond (head y)
               ff                          -- y is negative and x is not
               (bv_ult (tail x) (tail y))) -- both positive
  definition bv_sgt : bv (succ n) → bv (succ n) → bool := λx y, bv_slt y x
  definition bv_sle : bv (succ n) → bv (succ n) → bool := λx y, bnot (bv_slt y x)
  definition bv_sge : bv (succ n) → bv (succ n) → bool := λx y, bv_sle y x
end arith


section from_bv
  variable {A : Type}

  -- Convert a bitvector to another number.
  definition from_bv [p : has_add A] [q0 : has_zero A] [q1 : has_one A] {n:nat} (v:bv n) : A :=
    let f := λr b, cond b (r + r + 1) (r + r) in
    foldl f 0 (to_list v)
end from_bv

end bv
