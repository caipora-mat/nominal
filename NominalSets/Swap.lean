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

### Basic properties

* `swap_coe` — coercion of `swap a b` to `Equiv.Perm α` equals `Equiv.swap a b`.
* `swap_self` — `swap a a = 1`.
* `swap_eq_one_iff` — `swap a b = 1 ↔ a = b`.
* `swap_ne_one` — `a ≠ b → swap a b ≠ 1`.
* `swap_mul_self` — `swap a b * swap a b = 1`.
* `swap_inv` — `(swap a b)⁻¹ = swap a b`.
* `swap_smul_swap_smul` — `swap a b • (swap a b • x) = x` for any perm-set element.
* `swap_comm` — `swap a b = swap b a`.

### Action on atoms

* `swap_smul_eq_of_not_mem` — a swap of atoms outside a set `s` fixes each element of `s`.
* `swap_apply_left` / `swap_apply_right` — action form: `swap a b • a = b` and `swap a b • b = a`.
* `swap_apply_of_ne` — action form: a swap fixes atoms different from both arguments.
* `swap_smul_def` — `swap a b • c = if c = a then b else if c = b then a else c`.
* `swap_apply_left'` / `swap_apply_right'` — function-application form of `swap_apply_left` / `swap_apply_right`.
* `swap_apply_of_ne'` — function-application form of `swap_apply_of_ne`.

### Conjugation and factorisation

* `swap_conj_eq_of_fixed` — conjugating a permutation by a swap that fixes both arguments is a no-op.
* `swap_mul_swap_comm` — commutativity lemma for products of swaps sharing one argument.
* `swap_triple_factorization` — `swap a a' = swap a a'' * swap a' a'' * swap a a''` for distinct `a`, `a'`, `a''`.
* `swap_equivariant` — `π • swap a b = swap (π • a) (π • b)`.

### movedFinset lemmas

* `movedFinset_swap` — `movedFinset (swap a b) = {a, b}` when `a ≠ b`.
* `movedFinset_swap_self` — `movedFinset (swap a a) = ∅`.
* `movedFinset_swap_smul_subset` — left-composing `swap a (σ a)` strictly shrinks the moved-point set of `σ`.
* `not_mem_movedFinset_swap_smul` — after left-composing `swap a (σ a)`, `a` is fixed.
* `swap_mul_cancel` — `σ = swap a (σ a) * (swap a (σ a) * σ)` (swap is its own inverse).

## References

* [A. M. Pitts, *Nominal Sets*][Pitts2013], Chapter 2.
-/

namespace NominalSets

open PermType

variable {α : Type*} [Name α]

/-- Bundled transposition in `FinitePerm α`. -/
def swap (a b : α) : FinitePerm α := ⟨Equiv.swap a b, FinitePerm.swap_finite a b⟩

/-- The coercion of `swap a b` to `Equiv.Perm α` is `Equiv.swap a b`. -/
@[simp, norm_cast]
theorem swap_coe (a b : α) : ((swap a b : FinitePerm α) : Equiv.Perm α) = Equiv.swap a b := rfl

/-- A transposition of atoms outside `s` fixes `s` pointwise. -/
@[simp]
theorem swap_smul_eq_of_not_mem {s : Set α} {a b : α} (ha : a ∉ s) (hb : b ∉ s) (c : α) (hc : c ∈ s) :
  (swap a b) • c = c := by
    simp only [PermType.atoms_smul]
    exact Equiv.swap_apply_of_ne_of_ne (fun h ↦ ha (h ▸ hc)) (fun h ↦ hb (h ▸ hc))

/-- Swapping an atom with itself is the identity: `swap a a = 1`. -/
@[simp]
theorem swap_self (a : α) : swap a a = (1 : FinitePerm α) := Subtype.ext (by simp [Equiv.swap_self]; rfl)

/-- `swap a b = 1` if and only if `a = b`. -/
@[simp]
theorem swap_eq_one_iff {a b : α} : swap a b = 1 ↔ a = b := by
  constructor
  · intro h
    by_contra hab
    have : (swap a b) a = (1 : FinitePerm α) a := congr_arg (· a) h
    simp [swap] at this
    exact hab this.symm
  · rintro rfl; exact swap_self a

/-- `swap a b ≠ 1` when `a ≠ b`. -/
theorem swap_ne_one {a b : α} (h : a ≠ b) : swap a b ≠ 1 :=
  swap_eq_one_iff.not.mpr h

/-- Swaps are self-inverse: `swap a b * swap a b = 1`. -/
@[simp, grind =]
theorem swap_mul_self (a b : α) : swap a b * swap a b = 1 := Subtype.ext (by simp)

/-- The inverse of a swap is itself: `(swap a b)⁻¹ = swap a b`. -/
@[simp, grind =]
theorem swap_inv (a b : α) : (swap a b)⁻¹ = swap a b := inv_eq_of_mul_eq_one_right (swap_mul_self a b)

/-- Applying a swap twice is the identity: `swap a b • (swap a b • x) = x`. -/
@[simp]
theorem swap_smul_swap_smul {X : Type*} [PermType α X] (a b : α) (x : X) : (swap a b) • ((swap a b) • x) = x := by
  rw [← mul_smul, swap_mul_self, one_smul]

/-- Swaps are symmetric: `swap a b = swap b a`. -/
@[grind =]
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

/-- Unfolded form of a swap on atoms: case-split on whether `c = a` or `c = b`. -/
theorem swap_smul_def (a b c : α) : (swap a b) • c = if c = a then b else if c = b then a else c := by
  simp [PermType.atoms_smul, swap, Equiv.swap_apply_def]

/-! #### Function-application variants

The lemmas above use `•` (the `PermType` action on atoms).  After `FinitePerm.ext` the goal
contains bare function application `(swap a b) c` via `FunLike`.  The following `@[simp]`
lemmas handle that form directly, avoiding a manual bridge through `PermType.atoms_smul`. -/

/-- Function-application form: `(swap a b) a = b`. -/
@[simp]
theorem swap_apply_left' (a b : α) : (swap a b) a = b := by simp [swap]

/-- Function-application form: `(swap a b) b = a`. -/
@[simp]
theorem swap_apply_right' (a b : α) : (swap a b) b = a := by simp [swap]

/-- Function-application form: `(swap a b) c = c` when `c ≠ a` and `c ≠ b`. -/
@[simp]
theorem swap_apply_of_ne' {a b c : α} (ha : c ≠ a) (hb : c ≠ b) : (swap a b) c = c :=
  Equiv.swap_apply_of_ne_of_ne ha hb

/-- Conjugating `σ` by `swap a b` is trivial when both `a` and `b` are fixed by `σ`. -/
@[grind =]
theorem swap_conj_eq_of_fixed {σ : FinitePerm α} {a b : α} (ha : σ a = a) (hb : σ b = b) : swap a b * σ * swap a b = σ := by
  ext c
  simp only [mul_apply]
  by_cases hca : c = a
  · rw [hca, swap_apply_left', hb, swap_apply_right', ha]
  · by_cases hcb : c = b
    · rw [hcb, swap_apply_right', ha, swap_apply_left', hb]
    · have hσc_ne_a : σ c ≠ a := fun h ↦ hca (σ.val.injective (h.trans ha.symm))
      have hσc_ne_b : σ c ≠ b := fun h ↦ hcb (σ.val.injective (h.trans hb.symm))
      rw [swap_apply_of_ne' hca hcb, swap_apply_of_ne' hσc_ne_a hσc_ne_b]

/-- The moved-point set of `swap a b` is `{a, b}` when `a ≠ b`. -/
@[simp]
theorem movedFinset_swap {a b : α} (h : a ≠ b) : movedFinset (swap a b) = {a, b} := by
  ext c; simp only [mem_movedFinset, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hc
    by_contra habs; push_neg at habs
    exact hc (swap_apply_of_ne' habs.1 habs.2)
  · rintro (rfl | rfl) <;> simp [swap, h, h.symm]

/-- The moved-point set of `swap a a` is empty. -/
@[simp]
theorem movedFinset_swap_self (a : α) : movedFinset (swap a a) = ∅ := by simp [swap_self]

/-- Left-composing `swap a (σ a)` strictly shrinks the moved-point set: `movedFinset (swap a (σ a) * σ) ⊆ movedFinset σ`. -/
theorem movedFinset_swap_smul_subset {σ : FinitePerm α} {a : α} (hmoved : σ a ≠ a) : movedFinset (swap a (σ a) * σ) ⊆ movedFinset σ := by
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
theorem not_mem_movedFinset_swap_smul (σ : FinitePerm α) (a : α) : a ∉ movedFinset (swap a (σ a) * σ) := by
  rw [mem_movedFinset, not_not]
  change (Equiv.swap a (σ a)) (σ a) = a
  exact Equiv.swap_apply_right a (σ a)

/-- A permutation equals `swap a (σ a)` composed with `swap a (σ a) * σ`, because `swap` is its own inverse. -/
theorem swap_mul_cancel (σ : FinitePerm α) (a : α) : σ = swap a (σ a) * (swap a (σ a) * σ) := by
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
@[simp]
theorem swap_equivariant (π : FinitePerm α) (a b : α) : π • swap a b = swap (π • a) (π • b) := by
  apply Subtype.ext
  simp only [PermType.conj_smul, PermType.atoms_smul]
  exact (Equiv.swap_apply_apply π a b).symm

/-- Swap permutation identity: `swap a₁ a' * swap a₁ a₂ = swap a₂ a' * swap a₁ a'`
when `a' ≠ a₁` and `a' ≠ a₂`. Used in the well-definedness proof of concretion. -/
theorem swap_mul_swap_comm {a₁ a₂ a' : α} (hne : a₁ ≠ a₂) (ha₁ : a' ≠ a₁) (ha₂ : a' ≠ a₂) :
    swap a₁ a' * swap a₁ a₂ = swap a₂ a' * swap a₁ a' := by
  apply Subtype.ext; apply Equiv.Perm.ext; intro d
  simp only [swap_coe, Subgroup.coe_mul, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  split_ifs <;> simp_all

end NominalSets
