/-
Authors : Sayantan Khan

Formalizing (generalized) cohomology theory using Eilenberg-Steenrod axioms.
-/

import .type_ab_functor
import types.int

namespace ESaxioms

structure cohomology_groups (n : ℤ) :=
  type_ab_functor

end ESaxioms
