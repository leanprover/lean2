/-
Copyright (c) 2018 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

We pull back the structure of a category B along a map between the types A and (ob B).
We shorten the word "pullback" to "pb" to keep names relatively short.
-/


import ..functor.equivalence

open category eq is_trunc is_equiv sigma function equiv prod

namespace category
  open functor

  definition pb_precategory [constructor] {A B : Type} (f : A → B) (C : precategory B) :
    precategory A :=
  precategory.mk (λa a', hom (f a) (f a')) (λa a' a'' h g, h ∘ g) (λa, ID (f a))
    (λa a' a'' a''' k h g, assoc k h g) (λa a' g, id_left g) (λa a' g, id_right g)

  definition pb_Precategory [constructor] {A : Type} (C : Precategory) (f : A → C) :
    Precategory :=
  Precategory.mk A (pb_precategory f C)

  definition pb_Precategory_functor [constructor] {A : Type} (C : Precategory) (f : A → C) :
    pb_Precategory C f ⇒ C :=
  functor.mk f (λa a' g, g) proof (λa, idp) qed proof (λa a' a'' h g, idp) qed

  definition fully_faithful_pb_Precategory_functor {A : Type} (C : Precategory)
    (f : A → C) : fully_faithful (pb_Precategory_functor C f) :=
  begin intro a a', apply is_equiv_id end

  definition split_essentially_surjective_pb_Precategory_functor {A : Type} (C : Precategory)
    (f : A → C) (H : is_split_surjective f) :
    split_essentially_surjective (pb_Precategory_functor C f) :=
  begin intro c, cases H c with a p, exact ⟨a, iso.iso_of_eq p⟩ end

  definition is_equivalence_pb_Precategory_functor {A : Type} (C : Precategory)
    (f : A → C) (H : is_split_surjective f) : is_equivalence (pb_Precategory_functor C f) :=
  @(is_equivalence_of_fully_faithful_of_split_essentially_surjective _)
    (fully_faithful_pb_Precategory_functor C f)
    (split_essentially_surjective_pb_Precategory_functor C f H)

  definition pb_Precategory_equivalence [constructor] {A : Type} (C : Precategory) (f : A → C)
    (H : is_split_surjective f) : pb_Precategory C f ≃c C :=
  equivalence.mk _ (is_equivalence_pb_Precategory_functor C f H)

  definition pb_Precategory_equivalence_of_equiv [constructor] {A : Type} (C : Precategory)
    (f : A ≃ C) : pb_Precategory C f ≃c C :=
  pb_Precategory_equivalence C f (is_split_surjective_of_is_retraction f)

  definition is_isomorphism_pb_Precategory_functor [constructor] {A : Type} (C : Precategory)
    (f : A ≃ C) : is_isomorphism (pb_Precategory_functor C f) :=
  (fully_faithful_pb_Precategory_functor C f, to_is_equiv f)

  definition pb_Precategory_isomorphism [constructor] {A : Type} (C : Precategory) (f : A ≃ C) :
    pb_Precategory C f ≅c C :=
  isomorphism.mk _ (is_isomorphism_pb_Precategory_functor C f)

end category
