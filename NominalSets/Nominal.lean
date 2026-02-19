import NominalSets.PermType
import Mathlib.GroupTheory.GroupAction.Support
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Equiv.Basic

/-!
# Nominal Sets

A **nominal set** is a permutation type in which every element has **finite support**:
there exists a finite set of atoms that supports it in the sense of `MulAction.Supports`.

## Main definitions

* `Nominal α X` — typeclass: a `PermType α X` in which every element is finitely supported.

## Instances

* `Nominal.instAtoms` — atoms `α` form a nominal set (atom `a` is supported by `{a}`).
* `Nominal.instProd` — products of nominal sets are nominal (support is the union of supports).

## References

* [A. M. Pitts, *Nominal Sets*][Pitts2013], Chapter 2.
-/

/-- A **nominal set** is a permutation type in which every element is finitely supported. -/
class Nominal (α : Type*) [Name α] (X : Type*) extends PermType α X where
  finSupp : ∀ x : X, FinSupported (α := α) x

namespace Nominal

variable {α : Type*} [Name α]

variable {X Y : Type*}

/-- Atoms form a nominal set: atom `a` is supported by the singleton `{a}`. -/
instance instAtoms : Nominal α α where
  __ := PermType.instAtoms
  finSupp a := ⟨{a}, fun π h ↦ by
    simp only [PermType.atoms_smul]
    apply h
    simp⟩

/-- Products of nominal sets are nominal: take the union of the respective supports. -/
instance instProd [Nominal α X] [Nominal α Y] : Nominal α (X × Y) where
  __ := PermType.instProd
  finSupp := fun ⟨x, y⟩ ↦ by
    obtain ⟨sx, hsx⟩ := Nominal.finSupp (α := α) x
    obtain ⟨sy, hsy⟩ := Nominal.finSupp (α := α) y
    exact ⟨sx ∪ sy, fun π hπ ↦ by
      simp only [PermType.prod_smul]
      congr
      · exact hsx π (fun a ha ↦ hπ (Finset.mem_union_left _ ha))
      · exact hsy π (fun a ha ↦ hπ (Finset.mem_union_right _ ha))⟩

end Nominal
