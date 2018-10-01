algebra
=======

The following files are [ported](../port.md) from the standard library. If anything needs to be changed, it is probably a good idea to change it in the standard library and then port the file again (see also [script/port.pl](../../script/port.pl)).

* [priority](priority.hlean) : priority for algebraic operations
* [relation](relation.hlean)
* [binary](binary.hlean) : binary operations
* [order](order.hlean)
* [lattice](lattice.hlean)
* [group](group.hlean)
* [ring](ring.hlean)
* [ordered_group](ordered_group.hlean)
* [ordered_ring](ordered_ring.hlean)
* [field](field.hlean)
* [ordered_field](ordered_field.hlean)
* [bundled](bundled.hlean) : bundled versions of the algebraic structures
* [homomorphism](homomorphism.hlean)
* [group_power](group_power.hlean) (depends on files in [nat](../types/nat/nat.md) and [int](../types/int/int.md))

Files which are not ported from the standard library:

* [inf_group](inf_group.hlean) : algebraic structures which are not assumes to be sets. No higher coherences are assumed. Truncated algebraic structures extend these structures with the assumption that they are sets.
* [inf_group_theory](inf_group_theory.hlean) : Some very basic group theory using InfGroups
* [group_theory](group_theory.hlean) : Basic theorems about group homomorphisms and isomorphisms
* [trunc_group](trunc_group.hlean) : truncate an infinity-group to a group
* [homotopy_group](homotopy_group.hlean) : homotopy groups of a pointed type
* [e_closure](e_closure.hlean) : the type of words formed by a relation, or paths in a graph.
* [graph](graph.hlean) : definition and operations on paths in a graph.

Subfolders (not ported):

* [category](category/category.md) : Category Theory
