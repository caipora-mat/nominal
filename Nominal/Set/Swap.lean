import Nominal.Set.PermType
import Nominal.Set.Equivariant

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
* `swap_smul_ne_iff` — `swap a b • c ≠ c ↔ a ≠ b ∧ (c = a ∨ c = b)`.
* `swap_smul_eq_left_iff` — `swap a b • c = a ↔ c = b ∨ (c = a ∧ a = b)`.
* `swap_smul_eq_right_iff` — `swap a b • c = b ↔ c = a ∨ (c = b ∧ a = b)`.
* `swap_apply_left'` / `swap_apply_right'` — function-application form of `swap_apply_left` / `swap_apply_right`.
* `swap_apply_of_ne'` — function-application form of `swap_apply_of_ne`.

### Conjugation and factorisation

* `swap_conj_eq_of_fixed` — conjugating a permutation by a swap that fixes both arguments is a no-op.
* `swap_conj_mul` — multiplicative form: `π * swap a b = swap (π • a) (π • b) * π`.
* `swap_mul_swap_comm` — commutativity lemma for products of swaps sharing one argument.
* `swap_triple_factorization` — `swap a a' = swap a a'' * swap a' a'' * swap a a''` for distinct `a`, `a'`, `a''`.
* `swap_equivariant` — `π • swap a b = swap (π • a) (π • b)`.
* `isEquivariant₂_swap` — `swap` is an equivariant binary function (`IsEquivariant₂` packaging).
* `isEquivariant_swap_smul` — the map `(a, b, x) ↦ swap a b • x` is equivariant as `α × α × X → X`.
* `swap_smul_equivariant` — `swap (π • a) (π • b) • (π • x) = π • (swap a b • x)`.
* `swap_eq_swap_iff` — `swap a b = swap c d ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) ∨ (a = b ∧ c = d)`.
* `swap_smul_prod` — the swap action distributes over pairs: `swap a b • (x, y) = (swap a b • x, swap a b • y)`.
* `swap_mul_eq_self_iff` — `swap a b * σ = σ ↔ a = b`.
* `mul_swap_eq_self_iff` — `σ * swap a b = σ ↔ a = b`.
* `swap_smul_eq_iff` — `swap a b • x = y ↔ x = swap a b • y`.

### movedFinset lemmas

* `movedFinset_swap_subset` — `movedFinset (swap a b) ⊆ {a, b}` (without requiring `a ≠ b`).
* `movedFinset_swap` — `movedFinset (swap a b) = {a, b}` when `a ≠ b`.
* `movedFinset_swap_self` — `movedFinset (swap a a) = ∅`.
* `movedFinset_swap_card` — `(movedFinset (swap a b)).card = 2` when `a ≠ b`.
* `movedFinset_swap_smul_subset` — `movedFinset (swap a (σ a) * σ) ⊆ movedFinset σ` when `σ a ≠ a`.
* `movedFinset_swap_smul_ssubset` — `movedFinset (swap a (σ a) * σ) ⊂ movedFinset σ` when `σ a ≠ a` (strict version).
* `not_mem_movedFinset_swap_smul` — after left-composing `swap a (σ a)`, `a` is fixed.
* `swap_mul_cancel` — `σ = swap a (σ a) * (swap a (σ a) * σ)` (swap is its own inverse).
* `equivariantRel_swap_smul_eq` — the relation `swap a₁ d • x₁ = swap a₂ d • x₂` is equivariant.

## References

* [A. M. Pitts, *Nominal Sets*][Pitts2013], Chapter 2.
-/

namespace Nominal.Set
open Core PermType

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
theorem swap_self (a : α) : swap a a = (1 : FinitePerm α) := by ext c; simp [swap]

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
theorem swap_ne_one {a b : α} (h : a ≠ b) : swap a b ≠ 1 := swap_eq_one_iff.not.mpr h

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
theorem swap_comm (a b : α) : swap a b = swap b a := by ext c; simp [swap, Equiv.swap_comm]

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

/-- A swap moves atom `c` iff `a ≠ b` and `c` is one of `a`, `b`.
    PermType-level lift of `Equiv.swap_apply_ne_self_iff`. -/
@[simp]
theorem swap_smul_ne_iff {a b c : α} : (swap a b) • c ≠ c ↔ a ≠ b ∧ (c = a ∨ c = b) := by
  simp only [PermType.atoms_smul, ne_eq]
  exact Equiv.swap_apply_ne_self_iff

/-- `swap a b` sends `c` to `a` iff `c = b` or (`c = a` and `a = b`). -/
theorem swap_smul_eq_left_iff {a b c : α} : (swap a b) • c = a ↔ c = b ∨ (c = a ∧ a = b) := by
  constructor
  · intro h
    by_cases hcb : c = b
    · exact Or.inl hcb
    · by_cases hca : c = a
      · subst hca; rw [swap_apply_left] at h; exact Or.inr ⟨rfl, h.symm⟩
      · rw [swap_apply_of_ne hca hcb] at h; exact absurd h.symm (Ne.symm hca)
  · rintro (rfl | ⟨rfl, rfl⟩)
    · exact swap_apply_right _ _
    · simp

/-- `swap a b` sends `c` to `b` iff `c = a` or (`c = b` and `a = b`). -/
theorem swap_smul_eq_right_iff {a b c : α} : (swap a b) • c = b ↔ c = a ∨ (c = b ∧ a = b) := by
  rw [swap_comm a b, swap_smul_eq_left_iff]
  constructor
  · rintro (rfl | ⟨rfl, hab⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨rfl, hab.symm⟩
  · rintro (rfl | ⟨rfl, hab⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨rfl, hab.symm⟩

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
  simp only [FinitePerm.mul_apply]
  by_cases hca : c = a
  · rw [hca, swap_apply_left', hb, swap_apply_right', ha]
  · by_cases hcb : c = b
    · rw [hcb, swap_apply_right', ha, swap_apply_left', hb]
    · have hσc_ne_a : σ c ≠ a := fun h ↦ hca (σ.val.injective (h.trans ha.symm))
      have hσc_ne_b : σ c ≠ b := fun h ↦ hcb (σ.val.injective (h.trans hb.symm))
      rw [swap_apply_of_ne' hca hcb, swap_apply_of_ne' hσc_ne_a hσc_ne_b]

/-- The moved-point set of `swap a b` is contained in `{a, b}`, without requiring `a ≠ b`. -/
theorem movedFinset_swap_subset (a b : α) : movedFinset (swap a b) ⊆ {a, b} := by
  intro c hc
  simp only [mem_movedFinset] at hc
  simp only [Finset.mem_insert, Finset.mem_singleton]
  by_contra habs
  push Not at habs
  exact hc (swap_apply_of_ne' habs.1 habs.2)

/-- The moved-point set of `swap a b` is `{a, b}` when `a ≠ b`. -/
@[simp]
theorem movedFinset_swap {a b : α} (h : a ≠ b) : movedFinset (swap a b) = {a, b} := by
  ext c; simp only [mem_movedFinset, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hc
    by_contra habs; push Not at habs
    exact hc (swap_apply_of_ne' habs.1 habs.2)
  · rintro (rfl | rfl) <;> simp [swap, h, h.symm]

/-- The moved-point set of `swap a a` is empty. -/
@[simp]
theorem movedFinset_swap_self (a : α) : movedFinset (swap a a) = ∅ := by simp [swap_self]

/-- Left-composing `swap a (σ a)` strictly shrinks the moved-point set: `movedFinset (swap a (σ a) * σ) ⊆ movedFinset σ`. -/
theorem movedFinset_swap_smul_subset {σ : FinitePerm α} {a : α} (hmoved : σ a ≠ a) : movedFinset (swap a (σ a) * σ) ⊆ movedFinset σ := by
  intro c hc
  rw [mem_movedFinset] at hc ⊢
  change (Equiv.swap a (σ a)) (σ c) ≠ c at hc
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
  apply Subtype.ext; ext c; simp [swap_coe]

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

/-- The `swap` function is equivariant as a binary function:
`swap (π • a) (π • b) = π • swap a b`. This is the `IsEquivariant₂` packaging of
`swap_equivariant`. -/
theorem isEquivariant₂_swap : IsEquivariant₂ α (swap : α → α → FinitePerm α) where
  map_smul π a b := (swap_equivariant π a b).symm

/-- Swap permutation identity: `swap a₁ a' * swap a₁ a₂ = swap a₂ a' * swap a₁ a'`
when `a' ≠ a₁` and `a' ≠ a₂`. Used in the well-definedness proof of concretion. -/
theorem swap_mul_swap_comm {a₁ a₂ a' : α} (hne : a₁ ≠ a₂) (ha₁ : a' ≠ a₁) (ha₂ : a' ≠ a₂) :
    swap a₁ a' * swap a₁ a₂ = swap a₂ a' * swap a₁ a' := by
  apply Subtype.ext; apply Equiv.Perm.ext; intro d
  simp only [swap_coe, Subgroup.coe_mul, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  split_ifs <;> simp_all

/-- Multiplicative form of swap equivariance (Pitts Prop. 1.16):
    `π * swap a b = swap (π • a) (π • b) * π`. -/
theorem swap_conj_mul (π : FinitePerm α) (a b : α) : π * swap a b = swap (π • a) (π • b) * π := by
  have h : π * swap a b * π⁻¹ = swap (π • a) (π • b) := by
    rw [← conj_smul]; exact swap_equivariant π a b
  calc π * swap a b
      = π * swap a b * π⁻¹ * π := by rw [mul_assoc, inv_mul_cancel, mul_one]
    _ = swap (π • a) (π • b) * π := by rw [h]

/-- Reverse conjugation: `swap a b * π = π * swap (π⁻¹ • a) (π⁻¹ • b)`.
This is the reverse of `swap_conj_mul`. Useful when a swap appears on the *left*
of a permutation product and needs to be moved to the right. -/
theorem mul_swap_conj (π : FinitePerm α) (a b : α) :
    swap a b * π = π * swap (π⁻¹ • a) (π⁻¹ • b) := by
  have h := swap_conj_mul π (π⁻¹ • a) (π⁻¹ • b)
  simp only [PermType.smul_inv_smul] at h
  exact h.symm

/-- Applying a swap to a perm-set element is equivariant: `swap (π • a) (π • b) • (π • x) = π • (swap a b • x)`. -/
@[simp]
theorem swap_smul_equivariant {X : Type*} [PermType α X] (π : FinitePerm α) (a b : α) (x : X) :
    swap (π • a) (π • b) • (π • x) = π • (swap a b • x) := by
  rw [← swap_equivariant, conj_smul, mul_smul', mul_smul', PermType.inv_smul_smul]

/-- The map `(a, b, x) ↦ swap a b • x` is equivariant as a function `α × α × X → X`. -/
theorem isEquivariant_swap_smul {X : Type*} [PermType α X] : IsEquivariant α (fun (p : α × α × X) ↦ swap p.1 p.2.1 • p.2.2) where
  map_smul π p := by
    simp only [Prod.smul_fst, Prod.smul_snd]
    exact swap_smul_equivariant π p.1 p.2.1 p.2.2

/-- Two swaps are equal iff they swap the same unordered pair of atoms (or both arguments coincide). -/
theorem swap_eq_swap_iff {a b c d : α} : swap a b = swap c d ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) ∨ (a = b ∧ c = d) := by
  constructor
  · intro h
    -- Both sides are `FinitePerm`, evaluate at `a` and `b` via `DFunLike.congr_fun`
    have hfa : (swap a b) a = (swap c d) a := DFunLike.congr_fun h a
    have hfb : (swap a b) b = (swap c d) b := DFunLike.congr_fun h b
    simp only [swap_apply_left', swap_apply_right'] at hfa hfb
    -- hfa : b = (swap c d) a,   hfb : a = (swap c d) b
    by_cases hac : a = c
    · -- (swap c d) a = (swap a d) a = d, so b = d
      left; exact ⟨hac, by rw [hac, swap_apply_left'] at hfa; exact hfa⟩
    · by_cases had : a = d
      · -- (swap c d) a = (swap c a) a = c, so b = c
        right; left; exact ⟨had, by rw [had, swap_apply_right'] at hfa; exact hfa⟩
      · -- (swap c d) fixes a, so b = a
        have hfix : (swap c d) a = a := swap_apply_of_ne' hac had
        have hba : b = a := hfa.trans hfix
        right; right; refine ⟨hba.symm, ?_⟩
        have hab : a = b := hba.symm
        have : swap a b = 1 := hab ▸ swap_self a
        exact swap_eq_one_iff.mp (h ▸ this)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, h⟩)
    · rfl
    · exact swap_comm a b
    · simp [h]

/-- The swap action distributes over pairs (specialisation of `prod_smul` to swaps). -/
@[simp]
theorem swap_smul_prod {X Y : Type*} [PermType α X] [PermType α Y] (a b : α) (x : X) (y : Y) :
    swap a b • (x, y) = (swap a b • x, swap a b • y) := prod_smul (swap a b) x y

/-- Left-multiplying by `swap a b` is the identity on `σ` iff `a = b`. -/
theorem swap_mul_eq_self_iff {a b : α} {σ : FinitePerm α} : swap a b * σ = σ ↔ a = b := by
  constructor
  · intro h
    have : swap a b = 1 := mul_right_cancel (b := σ) (by rwa [one_mul])
    exact swap_eq_one_iff.mp this
  · rintro rfl; simp

/-- Right-multiplying by `swap a b` is the identity on `σ` iff `a = b`. -/
theorem mul_swap_eq_self_iff {a b : α} {σ : FinitePerm α} : σ * swap a b = σ ↔ a = b := by
  constructor
  · intro h
    have : swap a b = 1 := mul_left_cancel (a := σ) (by rwa [mul_one])
    exact swap_eq_one_iff.mp this
  · rintro rfl; simp

/-- A swap action can be moved to the other side: `swap a b • x = y ↔ x = swap a b • y`.
    Consequence of swaps being involutions. -/
theorem swap_smul_eq_iff {X : Type*} [PermType α X] {a b : α} {x y : X} : swap a b • x = y ↔ x = swap a b • y := by
  constructor
  · intro h; rw [← h, swap_smul_swap_smul]
  · intro h; rw [h, swap_smul_swap_smul]

/-- The moved-point set of a non-trivial swap has exactly two elements. -/
theorem movedFinset_swap_card {a b : α} (h : a ≠ b) : (movedFinset (swap a b)).card = 2 := by
  rw [movedFinset_swap h, Finset.card_pair h]

theorem movedFinset_swap_smul_ssubset {σ : FinitePerm α} {a : α} (hmoved : σ a ≠ a) : movedFinset (swap a (σ a) * σ) ⊂ movedFinset σ := by
  refine (movedFinset_swap_smul_subset hmoved).ssubset_of_ne fun h ↦ ?_
  have h₁ : a ∉ movedFinset (swap a (σ a) * σ) := not_mem_movedFinset_swap_smul σ a
  have h₂ : a ∈ movedFinset σ := mem_movedFinset.mpr hmoved
  exact h₁ (h ▸ h₂)

/-- The relation `(d, (a₁, x₁, a₂, x₂)) ↦ swap a₁ d • x₁ = swap a₂ d • x₂` is equivariant.
Used in `abs_eq_iff_exists` and `abs_eq_iff_forall` for the Some/Any characterisation of
abstraction equality. -/
theorem equivariantRel_swap_smul_eq {X : Type*} [PermType α X] : EquivariantRel α (fun (d : α) (t : α × X × α × X) ↦
    swap t.1 d • t.2.1 = swap t.2.2.1 d • t.2.2.2) where
  smul_iff π d t := by
    simp only [Prod.smul_fst, Prod.smul_snd]
    rw [swap_smul_equivariant, swap_smul_equivariant, smul_left_cancel_iff]

end Nominal.Set
