import NominalSets.PermType

import Mathlib.Logic.Equiv.Basic

/-!
# Transpositions in `FinitePerm α`

This file introduces the **swap** (transposition) as a bundled element of `FinitePerm α`
and proves the structural lemmas about the moved-point set `movedFinset` (defined in `NominalSets.PermType`)
that are needed for the swap characterisation of supports (Pitts, Prop. 2.1), proved in `NominalSets.Support`.

## Main definitions

* `swap a b` — the transposition of `a` and `b` as a `FinitePerm α`.

## Main results

* `swap_coe` — coercion of `swap a b` to `Equiv.Perm α` equals `Equiv.swap a b`.
* `swapFP_fixes_of_not_mem` — a transposition of atoms outside `s` fixes every element of `s`.
* `swap_self` — `swap a a = 1`.
* `swap_mul_self` — `swap a b * swap a b = 1`.
* `swap_inv` — `(swap a b)⁻¹ = swap a b`.
* `swap_comm` — `swap a b = swap b a`.
* `swap_apply_left` / `swap_apply_right` — action of a swap on its arguments.
* `swap_apply_of_ne` — a swap fixes atoms different from both arguments.
* `movedFinset_swap_smul_subset` — composing `swap a (σ a)` on the left strictly shrinks the moved-point set of `σ`.
* `not_mem_movedFinset_swap_smul` — after left-composing `swap a (σ a)`, `a` is fixed.
* `swap_mul_cancel` — `σ = swap a (σ a) * (swap a (σ a) * σ)`
* `swap_triple_factorization` — `swap a a' = swap a a'' * swap a' a'' * swap a a''` for distinct `a`, `a'`, `a''`.
* `swap_equivariant` — `π • swap a b = swap (π • a) (π • b)`.

## References

* [A. M. Pitts, *Nominal Sets*][Pitts2013], Chapter 2.
-/

namespace NominalSets

open PermType

variable {α : Type*} [Name α]

/-- Bundled transposition in `FinitePerm α`. -/
def swap (a b : α) : FinitePerm α := ⟨Equiv.swap a b, FinitePerm.swap_finite a b⟩

@[simp, norm_cast]
theorem swap_coe (a b : α) : ((swap a b : FinitePerm α) : Equiv.Perm α) = Equiv.swap a b := rfl

/-- A transposition of atoms outside `s` fixes `s` pointwise. -/
@[simp]
theorem swapFP_fixes_of_not_mem {s : Set α} {a b : α}
    (ha : a ∉ s) (hb : b ∉ s) (c : α) (hc : c ∈ s) : (swap a b) • c = c := by
  simp only [PermType.atoms_smul]
  exact Equiv.swap_apply_of_ne_of_ne (fun h ↦ ha (h ▸ hc)) (fun h ↦ hb (h ▸ hc))

theorem swap_self (a : α) : swap a a = (1 : FinitePerm α) := Subtype.ext (by simp [Equiv.swap_self]; rfl)

/-- Swaps are self-inverse: `swap a b * swap a b = 1`. -/
@[simp]
theorem swap_mul_self (a b : α) : swap a b * swap a b = 1 := Subtype.ext (by simp)

/-- The inverse of a swap is itself: `(swap a b)⁻¹ = swap a b`. -/
@[simp]
theorem swap_inv (a b : α) : (swap a b)⁻¹ = swap a b := inv_eq_of_mul_eq_one_right (swap_mul_self a b)

/-- Swaps are symmetric: `swap a b = swap b a`. -/
theorem swap_comm (a b : α) : swap a b = swap b a := Subtype.ext (by simp [Equiv.swap_comm])

/-- A swap sends `a` to `b`. -/
@[simp]
theorem swap_apply_left (a b : α) : (swap a b) • a = b := by simp [PermType.atoms_smul, swap]

/-- A swap sends `b` to `a`. -/
@[simp]
theorem swap_apply_right (a b : α) : (swap a b) • b = a := by simp [PermType.atoms_smul, swap]

/-- A swap fixes any atom different from both `a` and `b`. -/
@[simp]
theorem swap_apply_of_ne {a b c : α} (ha : c ≠ a) (hb : c ≠ b) : (swap a b) • c = c := by
  simp only [PermType.atoms_smul]
  exact Equiv.swap_apply_of_ne_of_ne ha hb

theorem movedFinset_swap_smul_subset {σ : FinitePerm α} {a : α} (hmoved : σ a ≠ a) :
    movedFinset (swap a (σ a) * σ) ⊆ movedFinset σ := by
  intro c hc
  rw [Set.Finite.mem_toFinset] at hc ⊢
  simp only [Equiv.Perm.movedPoints, Set.mem_setOf_eq,
             Subgroup.coe_mul, swap_coe, Equiv.Perm.mul_apply] at hc
  intro heq
  rw [heq, Equiv.swap_apply_def] at hc
  split_ifs at hc with h₁ h₂
  · subst_vars; contradiction
  · exact hmoved (σ.val.injective (show σ (σ a) = σ a from h₂ ▸ heq))
  · contradiction

/-- After composing `swap a (σ a)` on the left, `a` becomes a fixed point. -/
theorem not_mem_movedFinset_swap_smul {σ : FinitePerm α} {a : α} : a ∉ movedFinset (swap a (σ a) * σ) := by
  rw [mem_movedFinset, not_not]
  change (Equiv.swap a (σ a)) (σ a) = a
  exact Equiv.swap_apply_right a (σ a)

/-- A permutation equals `swap a (σ a)` composed with `swap a (σ a) * σ`, because `swap` is its own inverse. -/
theorem swap_mul_cancel {σ : FinitePerm α} {a : α} : σ = swap a (σ a) * (swap a (σ a) * σ) := by
  apply Subtype.ext
  ext c
  simp [swap_coe]

/-- **Swap factorization.** The transposition of `a` and `a'` can be written as a
product of three transpositions through a fresh atom `a''`:
`swap a a' = swap a a'' * swap a' a'' * swap a a''`. -/
theorem swap_triple_factorization {a a' a'' : α} (hne_a : a ≠ a') (hne_a' : a ≠ a'') (hne_a'' : a' ≠ a'') :
    swap a a' = swap a a'' * swap a' a'' * swap a a'' := by
  apply Subtype.ext
  apply Equiv.Perm.ext
  intro c
  simp only [swap_coe, Subgroup.coe_mul, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  split_ifs <;> simp_all

/-- The `swap` function is equivariant: `π • swap a b = swap (π • a) (π • b)` -/
theorem swap_equivariant (π : FinitePerm α) (a b : α) : π • swap a b = swap (π • a) (π • b) := by
  apply Subtype.ext
  simp only [PermType.conj_smul, PermType.atoms_smul]
  exact (Equiv.swap_apply_apply π a b).symm

end NominalSets
