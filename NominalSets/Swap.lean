import NominalSets.PermType

import Mathlib.Logic.Equiv.Basic

/-!
# Transpositions in `FinitePerm α`

This file introduces the **swap** (transposition) as a bundled element of `FinitePerm α`
and proves the structural lemmas about the moved-point set `movedFinset` (defined in
`NominalSets.PermType`) that are needed for the swap characterisation of supports
(Pitts, Prop. 2.1), proved in `NominalSets.Support`.

## Main definitions

* `swap a b` — the transposition of `a` and `b` as a bundled `FinitePerm α`.

## Main results

* `swapFP_val` — coercion of `swap a b` to `Equiv.Perm α` equals `Equiv.swap a b`.
* `swapFP_fixes_of_not_mem` — a transposition of atoms outside `s` fixes every element of `s`.
* `swap_self` — `swap a a = 1`.
* `movedFinset_swap_smul_subset` — composing `swap a (σ a)` on the left strictly shrinks
  the moved-point set of `σ`.
* `not_mem_movedFinset_swap_smul` — after left-composing `swap a (σ a)`, `a` is fixed.
* `swap_mul_cancel` — `σ = swap a (σ a) * (swap a (σ a) * σ)` (swap is self-inverse).
* `swap_triple_factorization` — `swap a a' = swap a a'' * swap a' a'' * swap a a''`
  for distinct `a`, `a'`, `a''`.

## References

* [A. M. Pitts, *Nominal Sets*][Pitts2013], Chapter 2.
-/

open PermType

variable {α : Type*} [Name α]

/-- Bundled transposition in `FinitePerm α`. -/
def swap (a b : α) : FinitePerm α := ⟨Equiv.swap a b, FinitePerm.swap_finite a b⟩

@[simp, norm_cast]
theorem swapFP_val (a b : α) : (swap a b : FinitePerm α) = Equiv.swap a b := rfl

/-- A transposition of atoms outside `s` fixes `s` pointwise. -/
@[simp, grind ., grind →]
theorem swapFP_fixes_of_not_mem {s : Set α} {a b : α}
    (ha : a ∉ s) (hb : b ∉ s) (c : α) (hc : c ∈ s) : (swap a b) • c = c := by
  simp only [PermType.atoms_smul]
  exact Equiv.swap_apply_of_ne_of_ne (fun h ↦ ha (h ▸ hc)) (fun h ↦ hb (h ▸ hc))

theorem swap_self (a : α) : swap a a = (1 : FinitePerm α) :=
  Subtype.ext (by simp [swapFP_val, Equiv.swap_self]; rfl)

/-- The transposition `swap a (σ a)` composed on the left with `σ` moves a
strict subset of the atoms that `σ` moves: every atom fixed by `σ` is also
fixed by the composition, and `a` itself is no longer moved. -/
theorem movedFinset_swap_smul_subset {σ : FinitePerm α} {a : α}
    (hmoved : σ a ≠ a) :
    movedFinset (swap a (σ a) * σ) ⊆ movedFinset σ := by
  intro c hc
  rw [Set.Finite.mem_toFinset] at hc ⊢
  simp only [Equiv.Perm.movedPoints, Set.mem_setOf_eq,
             Subgroup.coe_mul, swapFP_val, Equiv.Perm.mul_apply] at hc
  intro heq
  rw [heq, Equiv.swap_apply_def] at hc
  split_ifs at hc with h₁ h₂
  · subst_vars; contradiction
  · exact hmoved (σ.val.injective (show σ (σ a) = σ a from h₂ ▸ heq))
  · contradiction

/-- After composing `swap a (σ a)` on the left, `a` becomes a fixed point. -/
theorem not_mem_movedFinset_swap_smul {σ : FinitePerm α} {a : α} :
    a ∉ movedFinset (swap a (σ a) * σ) := by
  rw [mem_movedFinset, not_not]
  change (Equiv.swap a (σ a)) (σ a) = a
  exact Equiv.swap_apply_right a (σ a)

/-- A permutation equals `swap a (σ a)` composed with `swap a (σ a) * σ`,
because `swap` is its own inverse. -/
theorem swap_mul_cancel {σ : FinitePerm α} {a : α} :
    σ = swap a (σ a) * (swap a (σ a) * σ) := by
  apply Subtype.ext
  ext c
  simp [swapFP_val]

/-- **Swap factorization.** The transposition of `a` and `a'` can be written as a
product of three transpositions through a fresh atom `a''`:
`swap a a' = swap a a'' * swap a' a'' * swap a a''`. -/
theorem swap_triple_factorization {a a' a'' : α}
    (hne_a : a ≠ a') (hne_a' : a ≠ a'') (hne_a'' : a' ≠ a'') :
    swap a a' = swap a a'' * swap a' a'' * swap a a'' := by
  apply Subtype.ext
  apply Equiv.Perm.ext
  intro c
  simp only [swapFP_val, Subgroup.coe_mul, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  split_ifs <;> simp_all
