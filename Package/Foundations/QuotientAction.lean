/-
Copyright (c) 2026 Nominal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nominal contributors
-/
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Data.Quot
import Mathlib.GroupTheory.GroupAction.Hom

/-!
# Canonical actions on invariant quotients

An ordinary compatibility proof descends a selected scalar operation to
`Quotient s`. Monoid action laws then transfer along the surjective projection.
These are explicit constructors, not instances: each projection law fixes the
constructed action and makes no promise for another action on the same carrier.
No nominality, atom assumption, decidability or inhabitance is required.
-/

namespace NominalPackage

universe u v

/-- The selected scalar operation preserves the equivalence relation. -/
def SMulInvariant (M : Type u) {X : Type v} [SMul M X]
    (s : Setoid X) : Prop :=
  ∀ (m : M) ⦃x y : X⦄, s.r x y → s.r (m • x) (m • y)

namespace QuotientAction

section Scalars

variable {M : Type u} {X : Type v} [SMul M X]

/-- Descend a compatible scalar operation; install this constructor explicitly. -/
abbrev smul (s : Setoid X) (hs : SMulInvariant M s) : SMul M (Quotient s) where
  smul m := Quotient.map (sa := s) (sb := s) (m • ·) (hs m)

/-- The canonical quotient operation computes on a class constructor. -/
@[simp] theorem smul_mk (s : Setoid X) (hs : SMulInvariant M s) (m : M) (x : X) :
    letI := QuotientAction.smul s hs
    m • Quotient.mk s x = Quotient.mk s (m • x) := rfl

/-- The projection commutes with the canonical scalar operation. -/
theorem mk_smul (s : Setoid X) (hs : SMulInvariant M s) (m : M) (x : X) :
    letI := QuotientAction.smul s hs
    Quotient.mk s (m • x) = m • Quotient.mk s x := rfl

/-- The canonical projection in Mathlib's existing equivariant-map bundle. -/
def mkHom (s : Setoid X) (hs : SMulInvariant M s) :
    letI := QuotientAction.smul s hs
    X →[M] Quotient s :=
  letI := QuotientAction.smul s hs
  ⟨Quotient.mk s, fun _ _ => rfl⟩

@[simp] theorem mkHom_apply (s : Setoid X) (hs : SMulInvariant M s) (x : X) :
    QuotientAction.mkHom s hs x = Quotient.mk s x := rfl

end Scalars

/-- Transfer the source action laws to the canonical quotient scalar operation.
The inherited operation is definitionally `QuotientAction.smul s hs`. -/
abbrev mulAction {M : Type u} {X : Type v} [Monoid M] [MulAction M X]
    (s : Setoid X) (hs : SMulInvariant M s) : MulAction M (Quotient s) :=
  letI := QuotientAction.smul s hs
  Function.Surjective.mulAction (Quotient.mk s) Quotient.mk_surjective (mk_smul s hs)

end QuotientAction
end NominalPackage
