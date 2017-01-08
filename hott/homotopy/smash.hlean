/-
Copyright (c) 2016 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Floris van Doorn

The Smash Product of Types.

One definition is the cofiber of the map
    wedge A B → A × B
However, we define it (equivalently) as the pushout of the maps A + B → 2 and A + B → A × B.
-/

import homotopy.circle homotopy.join types.pointed homotopy.cofiber homotopy.wedge

open bool pointed eq equiv is_equiv sum bool prod unit circle cofiber prod.ops wedge

namespace smash

  variables {A B : Type*}

  section
  open pushout

  definition prod_of_sum [unfold 3] (u : A + B) : A × B :=
  by induction u with a b; exact (a, pt); exact (pt, b)

  definition bool_of_sum [unfold 3] (u : A + B) : bool :=
  by induction u; exact ff; exact tt

  definition smash' (A B : Type*) : Type := pushout (@prod_of_sum A B) (@bool_of_sum A B)
  protected definition mk' (a : A) (b : B) : smash' A B := inl (a, b)

  definition pointed_smash' [instance] [constructor] (A B : Type*) : pointed (smash' A B) :=
  pointed.mk (smash.mk' pt pt)
  definition smash [constructor] (A B : Type*) : Type* :=
  pointed.mk' (smash' A B)

  infixr ` ∧ ` := smash

  protected definition mk (a : A) (b : B) : A ∧ B := inl (a, b)
  definition auxl : smash A B := inr ff
  definition auxr : smash A B := inr tt
  definition gluel (a : A) : smash.mk a pt = auxl :> smash A B := glue (inl a)
  definition gluer (b : B) : smash.mk pt b = auxr :> smash A B := glue (inr b)

  end

  definition gluel' (a a' : A) : smash.mk a pt = smash.mk a' pt :> smash A B :=
  gluel a ⬝ (gluel a')⁻¹
  definition gluer' (b b' : B) : smash.mk pt b = smash.mk pt b' :> smash A B :=
  gluer b ⬝ (gluer b')⁻¹
  definition glue (a : A) (b : B) : smash.mk a pt = smash.mk pt b :=
  gluel' a pt ⬝ gluer' pt b

  definition glue_pt_left (b : B) : glue (Point A) b = gluer' pt b :=
  whisker_right _ !con.right_inv ⬝ !idp_con

  definition glue_pt_right (a : A) : glue a (Point B) = gluel' a pt :=
  proof whisker_left _ !con.right_inv qed

  definition ap_mk_left {a a' : A} (p : a = a') : ap (λa, smash.mk a (Point B)) p = gluel' a a' :=
  !ap_is_constant

  definition ap_mk_right {b b' : B} (p : b = b') : ap (smash.mk (Point A)) p = gluer' b b' :=
  !ap_is_constant

  protected definition rec {P : smash A B → Type} (Pmk : Πa b, P (smash.mk a b))
    (Pl : P auxl) (Pr : P auxr) (Pgl : Πa, Pmk a pt =[gluel a] Pl)
    (Pgr : Πb, Pmk pt b =[gluer b] Pr) (x : smash' A B) : P x :=
  begin
    induction x with x b u,
    { induction x with a b, exact Pmk a b },
    { induction b, exact Pl, exact Pr },
    { induction u: esimp,
      { apply Pgl },
      { apply Pgr }}
  end

  theorem rec_gluel {P : smash A B → Type} {Pmk : Πa b, P (smash.mk a b)}
    {Pl : P auxl} {Pr : P auxr} (Pgl : Πa, Pmk a pt =[gluel a] Pl)
    (Pgr : Πb, Pmk pt b =[gluer b] Pr) (a : A) :
    apd (smash.rec Pmk Pl Pr Pgl Pgr) (gluel a) = Pgl a :=
  !pushout.rec_glue

  theorem rec_gluer {P : smash A B → Type} {Pmk : Πa b, P (smash.mk a b)}
    {Pl : P auxl} {Pr : P auxr} (Pgl : Πa, Pmk a pt =[gluel a] Pl)
    (Pgr : Πb, Pmk pt b =[gluer b] Pr) (b : B) :
    apd (smash.rec Pmk Pl Pr Pgl Pgr) (gluer b) = Pgr b :=
  !pushout.rec_glue

  theorem rec_glue {P : smash A B → Type} {Pmk : Πa b, P (smash.mk a b)}
    {Pl : P auxl} {Pr : P auxr} (Pgl : Πa, Pmk a pt =[gluel a] Pl)
    (Pgr : Πb, Pmk pt b =[gluer b] Pr) (a : A) (b : B) :
    apd (smash.rec Pmk Pl Pr Pgl Pgr) (glue a b) =
      (Pgl a ⬝o (Pgl pt)⁻¹ᵒ) ⬝o (Pgr pt ⬝o (Pgr b)⁻¹ᵒ) :=
  by rewrite [↑glue, ↑gluel', ↑gluer', +apd_con, +apd_inv, +rec_gluel, +rec_gluer]

  protected definition elim {P : Type} (Pmk : Πa b, P) (Pl Pr : P)
    (Pgl : Πa : A, Pmk a pt = Pl) (Pgr : Πb : B, Pmk pt b = Pr) (x : smash' A B) : P :=
  smash.rec Pmk Pl Pr (λa, pathover_of_eq _ (Pgl a)) (λb, pathover_of_eq _ (Pgr b)) x

  -- an elim where you are forced to make (Pgl pt) and (Pgl pt) to be reflexivity
  protected definition elim' [reducible] {P : Type} (Pmk : Πa b, P)
    (Pgl : Πa : A, Pmk a pt = Pmk pt pt) (Pgr : Πb : B, Pmk pt b = Pmk pt pt)
    (ql : Pgl pt = idp) (qr : Pgr pt = idp) (x : smash' A B) : P :=
  smash.elim Pmk (Pmk pt pt) (Pmk pt pt) Pgl Pgr x

  theorem elim_gluel {P : Type} {Pmk : Πa b, P} {Pl Pr : P}
    (Pgl : Πa : A, Pmk a pt = Pl) (Pgr : Πb : B, Pmk pt b = Pr) (a : A) :
    ap (smash.elim Pmk Pl Pr Pgl Pgr) (gluel a) = Pgl a :=
  begin
    apply eq_of_fn_eq_fn_inv !(pathover_constant (@gluel A B a)),
    rewrite [▸*,-apd_eq_pathover_of_eq_ap,↑smash.elim,rec_gluel],
  end

  theorem elim_gluer {P : Type} {Pmk : Πa b, P} {Pl Pr : P}
    (Pgl : Πa : A, Pmk a pt = Pl) (Pgr : Πb : B, Pmk pt b = Pr) (b : B) :
    ap (smash.elim Pmk Pl Pr Pgl Pgr) (gluer b) = Pgr b :=
  begin
    apply eq_of_fn_eq_fn_inv !(pathover_constant (@gluer A B b)),
    rewrite [▸*,-apd_eq_pathover_of_eq_ap,↑smash.elim,rec_gluer],
  end

  theorem elim_glue {P : Type} {Pmk : Πa b, P} {Pl Pr : P}
    (Pgl : Πa : A, Pmk a pt = Pl) (Pgr : Πb : B, Pmk pt b = Pr) (a : A) (b : B) :
    ap (smash.elim Pmk Pl Pr Pgl Pgr) (glue a b) = (Pgl a ⬝ (Pgl pt)⁻¹) ⬝ (Pgr pt ⬝ (Pgr b)⁻¹) :=
  by rewrite [↑glue, ↑gluel', ↑gluer', +ap_con, +ap_inv, +elim_gluel, +elim_gluer]

end smash
open smash
attribute smash.mk smash.mk' auxl auxr [constructor]
attribute smash.elim' smash.rec smash.elim [unfold 9] [recursor 9]

namespace smash

  variables {A B : Type*}

  definition of_smash_pbool [unfold 2] (x : smash A pbool) : A :=
  begin
    induction x,
    { induction b, exact pt, exact a },
    { exact pt },
    { exact pt },
    { reflexivity },
    { induction b: reflexivity }
  end

  definition smash_pbool_pequiv [constructor] (A : Type*) : smash A pbool ≃* A :=
  begin
    fapply pequiv_of_equiv,
    { fapply equiv.MK,
      { exact of_smash_pbool },
      { intro a, exact smash.mk a tt },
      { intro a, reflexivity },
      { exact abstract begin intro x, induction x,
        { induction b, exact gluer' tt pt ⬝ gluel' pt a, reflexivity },
        { exact gluer' tt ff ⬝ gluel pt, },
        { exact gluer tt, },
        { apply eq_pathover_id_right,
          refine ap_compose (λa, smash.mk a tt) _ _ ⬝ ap02 _ !elim_gluel ⬝ph _,
          apply square_of_eq_top, refine !con.assoc⁻¹ ⬝ whisker_right _ !idp_con⁻¹ },
        { apply eq_pathover_id_right,
          refine ap_compose (λa, smash.mk a tt) _ _ ⬝ ap02 _ !elim_gluer ⬝ph _,
          induction b: esimp,
          { apply square_of_eq_top,
            refine whisker_left _ !con.right_inv ⬝ !con_idp ⬝ whisker_right _ !idp_con⁻¹ },
          { apply square_of_eq idp }} end end }},
    { reflexivity }
  end

end smash
