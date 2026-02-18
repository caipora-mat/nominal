import NominalSets.Wheels
import Mathlib.GroupTheory.Perm.ClosureSwap
import Mathlib.Topology.MetricSpace.Isometry

/-!
# Finite Permutations

A **finite permutation** of a name type `𝔸` is a permutation `π : Equiv.Perm 𝔸` that
moves only finitely many atoms, i.e., the set `{a : 𝔸 | π a ≠ a}` is finite.

Since `𝔸` is infinite (it satisfies `Name 𝔸`), we cannot use Mathlib's
`Equiv.Perm.support` (which requires `Fintype`). Instead, we characterise
finite permutations via `Set.Finite` on the complement of `MulAction.fixedBy`.

## Main definitions

* `FinitePerm 𝔸` — the subgroup of `Equiv.Perm 𝔸` consisting of permutations
  with finite support (finitely many non-fixed points).

## Main results

* `FinitePerm.swap_mem` — every transposition belongs to `FinitePerm 𝔸`.
* `FinitePerm.support_finite` — every member has finitely many non-fixed points.
-/

open Equiv MulAction Set

namespace Equiv.Perm

variable {𝔸 : Type*}

/-- The set of atoms moved by a permutation -/
def movedPoints (π : Perm 𝔸) : Set 𝔸 := {a | π a ≠ a}

/-- A permutation has **finite support** if it moves only finitely many atoms -/
def IsFinitePerm (π : Perm 𝔸) : Prop :=
  π.movedPoints.Finite

theorem movedPoints_eq_compl_fixedBy (π : Perm 𝔸) :
    π.movedPoints = (fixedBy 𝔸 π)ᶜ := by
  ext a
  simp [movedPoints, fixedBy, Perm.smul_def]

end Equiv.Perm

/-- `FinitePerm 𝔸` is the subgroup of `Equiv.Perm 𝔸` consisting of permutations
that move only finitely many atoms. -/
def FinitePerm (𝔸 : Type*) : Subgroup (Perm 𝔸) where
  carrier := {π | π.IsFinitePerm}
  one_mem' := by
    simp [Equiv.Perm.IsFinitePerm, Equiv.Perm.movedPoints]
  mul_mem' := by
    intro f g hf hg
    simp only [Set.mem_setOf_eq, Equiv.Perm.IsFinitePerm] at *
    apply Set.Finite.subset (hf.union hg)
    intro a ha
    simp only [Equiv.Perm.movedPoints, Set.mem_setOf_eq, Perm.mul_apply] at ha
    by_contra h
    push_neg at h
    obtain ⟨h1, h2⟩ := h
    simp only [Equiv.Perm.movedPoints, Set.mem_setOf_eq, not_not] at h1 h2
    exact ha (by rw [h2, h1])
  inv_mem' := by
    intro f hf
    simp only [Set.mem_setOf_eq, Equiv.Perm.IsFinitePerm, Equiv.Perm.movedPoints] at *
    apply Set.Finite.subset hf
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    intro heq
    rw [← heq, Equiv.Perm.inv_def, Equiv.symm_apply_apply] at ha
    symm at ha
    contradiction

namespace FinitePerm

variable {𝔸 : Type*}

/-- Every element of `FinitePerm 𝔸` moves finitely many atoms -/
theorem support_finite (π : FinitePerm 𝔸) : (π.val.movedPoints).Finite :=
  π.property

/-- Every transposition is a finite permutation (it moves at most 2 atoms) -/
theorem swap_mem (a b : 𝔸) [DecidableEq 𝔸] : Equiv.swap a b ∈ FinitePerm 𝔸 := by
  change (Equiv.swap a b).IsFinitePerm
  simp only [Equiv.Perm.IsFinitePerm, Equiv.Perm.movedPoints]
  apply Set.Finite.subset (({a, b} : Finset 𝔸).finite_toSet)
  intro x hx
  simp only [Set.mem_setOf_eq] at hx
  simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
  exact (swap_apply_ne_self_iff.mp hx).2

end FinitePerm
