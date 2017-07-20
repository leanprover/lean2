open unit pointed eq bool

structure foo (u v : unit) :=
 (b : bool → bool)

definition bar := foo star
definition bar.mk  [constructor] : bar star := foo.mk star star (λx, tt)
definition bar.mk2 [constructor] : bar star := bar.mk

example : foo.b bar.mk2 ff = tt :=
begin esimp end

definition my_ppi_const [constructor] {A : Type*} (P : A → Type*) : ppi P :=
ppi.mk (λa, pt) idp

definition my_pconst [constructor] (A B : Type*) : ppi (λ(a : A), B) :=
!my_ppi_const

example {A : Type*} (P : A → Type*) (a : A) : ppi.to_fun (my_ppi_const P) a = pt :=
begin esimp, end

example {A B : Type*} (a : A) : my_pconst A B a = pt :=
begin esimp end
