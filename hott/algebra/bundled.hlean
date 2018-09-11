/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

Bundled structures
-/
import algebra.ring
open algebra pointed is_trunc

namespace algebra
structure Semigroup :=
(carrier : Type) (struct : semigroup carrier)

attribute Semigroup.carrier [coercion]
attribute Semigroup.struct [instance]

structure CommSemigroup :=
(carrier : Type) (struct : comm_semigroup carrier)

attribute CommSemigroup.carrier [coercion]
attribute CommSemigroup.struct [instance]

structure Monoid :=
(carrier : Type) (struct : monoid carrier)

attribute Monoid.carrier [coercion]
attribute Monoid.struct [instance]

structure CommMonoid :=
(carrier : Type) (struct : comm_monoid carrier)

attribute CommMonoid.carrier [coercion]
attribute CommMonoid.struct [instance]

structure Group :=
(carrier : Type) (struct' : group carrier)

attribute Group.struct' [instance]

section
local attribute Group.carrier [coercion]
definition pSet_of_Group [constructor] [reducible] [coercion] (G : Group) : Set* :=
ptrunctype.mk (Group.carrier G) !semigroup.is_set_carrier 1
end

definition Group.struct [instance] [priority 2000] (G : Group) : group G :=
Group.struct' G

attribute algebra._trans_of_pSet_of_Group [unfold 1]
attribute algebra._trans_of_pSet_of_Group_1 algebra._trans_of_pSet_of_Group_2 [constructor]

definition pType_of_Group [reducible] [constructor] (G : Group) : Type* :=
G
definition Set_of_Group [reducible] [constructor] (G : Group) : Set :=
G

definition AddGroup : Type := Group

definition pSet_of_AddGroup [constructor] [reducible] [coercion] (G : AddGroup) : Set* :=
pSet_of_Group G

definition AddGroup.mk [constructor] [reducible] (G : Type) (H : add_group G) : AddGroup :=
Group.mk G H

definition AddGroup.struct [reducible] [instance] [priority 2000] (G : AddGroup) : add_group G :=
Group.struct G

attribute algebra._trans_of_pSet_of_AddGroup [unfold 1]
attribute algebra._trans_of_pSet_of_AddGroup_1 algebra._trans_of_pSet_of_AddGroup_2 [constructor]

definition pType_of_AddGroup [reducible] [constructor] : AddGroup → Type* :=
algebra._trans_of_pSet_of_AddGroup_1
definition Set_of_AddGroup [reducible] [constructor] : AddGroup → Set :=
algebra._trans_of_pSet_of_AddGroup_2

structure AbGroup :=
(carrier : Type) (struct' : ab_group carrier)

attribute AbGroup.struct' [instance]

section
local attribute AbGroup.carrier [coercion]
definition Group_of_AbGroup [coercion] [constructor] (G : AbGroup) : Group :=
Group.mk G _
end

definition AbGroup.struct [instance] [priority 2000] (G : AbGroup) : ab_group G :=
AbGroup.struct' G

attribute algebra._trans_of_Group_of_AbGroup_1
          algebra._trans_of_Group_of_AbGroup
          algebra._trans_of_Group_of_AbGroup_3 [constructor]
attribute algebra._trans_of_Group_of_AbGroup_2 [unfold 1]

definition AddAbGroup : Type := AbGroup

definition AddGroup_of_AddAbGroup [coercion] [constructor] (G : AddAbGroup) : AddGroup :=
Group_of_AbGroup G

definition AddAbGroup.struct [reducible] [instance] [priority 2000] (G : AddAbGroup) :
  add_ab_group G :=
AbGroup.struct G

definition AddAbGroup.mk [constructor] [reducible] (G : Type) (H : add_ab_group G) :
  AddAbGroup :=
AbGroup.mk G H

attribute algebra._trans_of_AddGroup_of_AddAbGroup_1
          algebra._trans_of_AddGroup_of_AddAbGroup
          algebra._trans_of_AddGroup_of_AddAbGroup_3 [constructor]
attribute algebra._trans_of_AddGroup_of_AddAbGroup_2 [unfold 1]

-- structure AddSemigroup :=
-- (carrier : Type) (struct : add_semigroup carrier)

-- attribute AddSemigroup.carrier [coercion]
-- attribute AddSemigroup.struct [instance]

-- structure AddCommSemigroup :=
-- (carrier : Type) (struct : add_comm_semigroup carrier)

-- attribute AddCommSemigroup.carrier [coercion]
-- attribute AddCommSemigroup.struct [instance]

-- structure AddMonoid :=
-- (carrier : Type) (struct : add_monoid carrier)

-- attribute AddMonoid.carrier [coercion]
-- attribute AddMonoid.struct [instance]

-- structure AddCommMonoid :=
-- (carrier : Type) (struct : add_comm_monoid carrier)

-- attribute AddCommMonoid.carrier [coercion]
-- attribute AddCommMonoid.struct [instance]

-- structure AddGroup :=
-- (carrier : Type) (struct : add_group carrier)

-- attribute AddGroup.carrier [coercion]
-- attribute AddGroup.struct [instance]

-- structure AddAbGroup :=
-- (carrier : Type) (struct : add_ab_group carrier)

-- attribute AddAbGroup.carrier [coercion]
-- attribute AddAbGroup.struct [instance]


-- some bundled infinity-structures
structure InfGroup :=
(carrier : Type) (struct' : inf_group carrier)

attribute InfGroup.struct' [instance]

section
  local attribute InfGroup.carrier [coercion]
  definition pType_of_InfGroup [constructor] [reducible] [coercion] (G : InfGroup) : Type* :=
  pType.mk G 1
end

attribute algebra._trans_of_pType_of_InfGroup [unfold 1]

definition InfGroup.struct [instance] [priority 2000] (G : InfGroup) : inf_group G :=
InfGroup.struct' G

definition AddInfGroup : Type := InfGroup

definition pType_of_AddInfGroup [constructor] [reducible] [coercion] (G : AddInfGroup) : Type* :=
pType_of_InfGroup G

definition AddInfGroup.mk [constructor] [reducible] (G : Type) (H : add_inf_group G) :
  AddInfGroup :=
InfGroup.mk G H

definition AddInfGroup.struct [reducible] (G : AddInfGroup) : add_inf_group G :=
InfGroup.struct G

attribute algebra._trans_of_pType_of_AddInfGroup [unfold 1]

structure AbInfGroup :=
(carrier : Type) (struct' : ab_inf_group carrier)

attribute AbInfGroup.struct' [instance]

section
local attribute AbInfGroup.carrier [coercion]
definition InfGroup_of_AbInfGroup [coercion] [constructor] (G : AbInfGroup) : InfGroup :=
InfGroup.mk G _
end

definition AbInfGroup.struct [instance] [priority 2000] (G : AbInfGroup) : ab_inf_group G :=
AbInfGroup.struct' G

attribute algebra._trans_of_InfGroup_of_AbInfGroup_1 [constructor]
attribute algebra._trans_of_InfGroup_of_AbInfGroup [unfold 1]

definition AddAbInfGroup : Type := AbInfGroup

definition AddInfGroup_of_AddAbInfGroup [coercion] [constructor] (G : AddAbInfGroup) : AddInfGroup :=
InfGroup_of_AbInfGroup G

definition AddAbInfGroup.struct [reducible] [instance] [priority 2000] (G : AddAbInfGroup) :
  add_ab_inf_group G :=
AbInfGroup.struct G

definition AddAbInfGroup.mk [constructor] [reducible] (G : Type) (H : add_ab_inf_group G) :
  AddAbInfGroup :=
AbInfGroup.mk G H

attribute algebra._trans_of_AddInfGroup_of_AddAbInfGroup_1 [constructor]
attribute algebra._trans_of_AddInfGroup_of_AddAbInfGroup [unfold 1]

definition InfGroup_of_Group [constructor] (G : Group) : InfGroup :=
InfGroup.mk G _

definition AddInfGroup_of_AddGroup [constructor] (G : AddGroup) : AddInfGroup :=
AddInfGroup.mk G _

definition AbInfGroup_of_AbGroup [constructor] (G : AbGroup) : AbInfGroup :=
AbInfGroup.mk G _

definition AddAbInfGroup_of_AddAbGroup [constructor] (G : AddAbGroup) : AddAbInfGroup :=
AddAbInfGroup.mk G _

/- rings -/
structure Ring :=
(carrier : Type) (struct : ring carrier)

attribute Ring.carrier [coercion]
attribute Ring.struct [instance]

end algebra
open algebra

namespace infgroup
attribute [coercion] InfGroup_of_Group
attribute [coercion] AbInfGroup_of_AbGroup
end infgroup
