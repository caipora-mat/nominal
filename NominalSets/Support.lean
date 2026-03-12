import NominalSets.Swap
import NominalSets.Equivariant

import Mathlib.GroupTheory.GroupAction.Support
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Card

/-!
# Support and the Swap Characterisation

This file introduces the `supports` relation and `FinSupported` predicate, and proves the key theorems about them.

The central result is the swap characterisation of supports (Pitts, Prop. 2.1): a finite
set `s` supports `x` if and only if every transposition of two atoms outside `s` fixes `x`.
The proof uses the `swap` and `movedFinset` machinery from `NominalSets.Swap` and
`NominalSets.PermType` via strong induction on the number of moved points.

## Main definitions

* `supports s x` — thin abbreviation for `MulAction.Supports (FinitePerm α) ↑s x` (where `s : Finset α`), specialising the acting group to `FinitePerm α`.
* `FinSupported x` — `x` is supported by some finite set of atoms.

## Main results

* `supports_iff_swap` — **Pitts, Prop. 2.1**: `s` supports `x` iff every transposition of two atoms outside `s` fixes `x`.
* `supports_mono` — if `s ⊆ t` and `s` supports `x`, then `t` supports `x`.
* `supports_inter` — the intersection of two finite supports is again a support.
* `supports_smul` — if `s` supports `x`, then `π • s` supports `π • x`.
* `supports_smul_iff` — `supports (π • s) (π • x) ↔ supports s x`.
* `equivariantRel_supports` — `supports` is an equivariant relation.
* `supports_empty_iff` — `∅` supports `x` iff every finite permutation fixes `x`.
* `supports_prod` — if `s` supports `x` and `t` supports `y`, then `s ∪ t` supports `(x, y)`.
* `supports_prod_iff` — `supports s (x, y) ↔ supports s x ∧ supports s y`.
* `supports_fst` / `supports_snd` — projections: if `s` supports a pair `(x, y)`, it supports each component.
* `supports_union_left` / `supports_union_right` — if `s` (resp. `t`) supports `x`, then `s ∪ t` supports `x`.
* `swap_smul_eq_of_supports` — if `s` supports `x` and `a`, `b ∉ s`, then `swap a b • x = x`.
* `supports_atom` — an atom `a` is supported by `{a}`.
* `supports_swap_pair` — `swap a b` is supported by `{a, b}`.
* `supports_inl` / `supports_inr` — injections into a sum preserve support.
* `supports_of_inl` / `supports_of_inr` — support of a sum injection implies support of the component.
* `supports_inl_iff` / `supports_inr_iff` — iff-variants for sum injections.
* `supports_none` — `∅` supports `none`.
* `supports_some` / `supports_of_some` — `some` preserves support in both directions.
* `supports_some_iff` — iff-variant for option injection.
* `supports_singleton_atom_iff` — `supports {a} (b : α) ↔ b = a`.
* `supports_finset_self` — a finset `s : Finset α` is supported by itself.
* `supports_erase_of_swap_fix` — removing an unnecessary atom from a support set.
* `supports_smul_of_supports_both` — if `s` supports both `π` and `x`, then `s` supports `π • x`.
* `IsEquivariant.supports_image` — an equivariant function preserves supports.
* `IsEquivariant.supports_of_image` — an injective equivariant function reflects supports.
* `IsEquivariant.supports_image_iff` — for injective equivariant `f`: `supports s (f x) ↔ supports s x`.
* `IsEquivariant₂.supports_image` — a binary equivariant function preserves supports.
* `FinSupported.smul` — finite support is preserved by the action.
* `FinSupported.of_smul` — if `π • x` is finitely supported, then `x` is finitely supported.
* `finSupported_smul_iff` — `FinSupported (π • x) ↔ FinSupported x`.
* `FinSupported.prod` / `FinSupported.fst` / `FinSupported.snd` — products and projections.
* `FinSupported.inl` / `FinSupported.inr` — sum injections preserve finite support.
* `FinSupported.of_inl` / `FinSupported.of_inr` — sum projections reflect finite support.
* `FinSupported.some` / `FinSupported.none` — option injections preserve finite support.
* `FinSupported.of_some` — option projection reflects finite support.
* `finSupported_prod_iff` / `finSupported_inl_iff` / `finSupported_inr_iff` / `finSupported_some_iff` — iff-variants.
* `FinSupported.atom` / `FinSupported.swap` — atoms and swaps are finitely supported.
* `IsEquivariant.finSupported` — an equivariant image of a finitely supported element is finitely supported.
* `IsEquivariant.finSupported_of_image` / `IsEquivariant.finSupported_iff` — injective equivariant reflects/iff for finite support.
* `IsEquivariant₂.finSupported` — binary equivariant preserves finite support.
* `equivariantPred_finSupported` — `FinSupported` is an equivariant predicate.

## References

* [A. M. Pitts, *Nominal Sets*][Pitts2013], Chapter 2.
-/

namespace NominalSets

section Support

open MulAction

variable {α : Type*} [Name α]

/-- `s` supports `b` with respect to the group `FinitePerm α`. A thin abbreviation over `MulAction.Supports` that fixes the acting group to `FinitePerm α`
and restricts the support set to a `Finset α`. -/
abbrev supports {β : Type*} [MulAction (FinitePerm α) β] (s : Finset α) (b : β) : Prop :=
  Supports (FinitePerm α) (s : Set α) b

/-- An element `x : X` is **finitely supported** if there exists a finite set of atoms
`s : Finset α` such that every finite permutation fixing `s` pointwise also fixes `x`. -/
def FinSupported {X : Type*} [PermType α X] (x : X) : Prop := ∃ s : Finset α, supports s x

/-- Monotonicity of support: if `s ⊆ t` and `s` supports `x`, then `t` supports `x`. -/
@[grind .] theorem supports_mono {β : Type*} [MulAction (FinitePerm α) β] {s t : Finset α} {x : β}
    (hst : s ⊆ t) (hs : supports s x) : supports t x :=
  Supports.mono (by exact_mod_cast Finset.coe_subset.mpr hst) hs

end Support

/-! ## Proposition 2.1 and the intersection of supports -/

section SwapChar

open MulAction PermType

variable {α : Type*} [Name α] {X : Type*} [PermType α X] {Y : Type*} [PermType α Y]

/-- **Pitts, Prop. 2.1.** A finset `s` supports `x` under `FinitePerm α` if and only if every transposition of two atoms *outside* `s` fixes `x`. -/
@[grind =] theorem supports_iff_swap {s : Finset α} {x : X} : supports s x ↔ ∀ a₁ a₂ : α, a₁ ∉ s → a₂ ∉ s → swap a₁ a₂ • x = x := by
  constructor
  -- (→) if s supports x and a₁, a₂ ∉ s, then swap a₁ a₂ fixes s
  -- (it only moves a₁ and a₂, which are outside s), so the support
  -- condition gives swap a₁ a₂ • x = x directly.
  · intro hs a₁ a₂ ha₁ ha₂
    exact hs _ fun c hcs ↦
      swap_smul_eq_of_not_mem (by simpa using ha₁) (by simpa using ha₂) c hcs
  -- (←) assuming every transposition of atoms outside s fixes x,
  -- show that every finite permutation σ that fixes s also fixes x.
  --
  -- Strategy: strong induction on |movedFinset σ| (π), peeling off one moved point
  -- at a time by left-multiplying by a suitable transposition.
  · intro hswap π hfix
    -- We generalise to an arbitrary σ (instead of π) so that the induction
    -- hypothesis applies to the smaller permutation σ' we construct below.
    suffices ∀ n : ℕ, ∀ σ : FinitePerm α,
        (movedFinset σ).card = n → (∀ c ∈ (s : Set α), σ • c = c) → σ • x = x by
      exact this _ π rfl (fun c hc ↦ hfix hc)
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
    intro σ hcard hσ
    -- Base case: σ has no moved points, so σ = 1 and σ • x = x trivially.
    by_cases hempty : movedFinset σ = ∅
    · simp [(movedFinset_eq_empty_iff_one.mp hempty)]
    -- Inductive step: σ has at least one moved point.
    · obtain ⟨z, hz⟩ := Finset.nonempty_of_ne_empty hempty
      have hmoved : σ z ≠ z := mem_movedFinset.mp hz
      -- Since σ fixes s, a moved point z cannot be in s (if z ∈ s then σ z = z, contradicting hmoved).
      -- Likewise σ z ∉ s: if σ z ∈ s then σ(σ z) = σ z, and injectivity gives σ z = z.
      have hz_not_s : z ∉ s := fun hin ↦ by
        have := hσ z (Finset.mem_coe.mpr hin)
        contradiction
      have hb_not_s : σ z ∉ s := fun hin ↦ by
        have := hσ (σ z) (Finset.mem_coe.mpr hin)
        simp only [PermType.atoms_smul, FinitePerm.apply_eq_iff_eq] at this
        exact hmoved this
      -- Because both z and (σ z) are not in s, our hypothesis gives:
      -- swap(z, σ z) fixes x.
      have hswap_x : swap z (σ z) • x = x := hswap z (σ z) hz_not_s hb_not_s
      -- Define the "reduced" permutation σ' = swap(z, σ z) * σ.
      -- Key idea: swap(z, σ z) undoes what σ does to z, so z becomes a fixed point of σ'.
      let σ' : FinitePerm α := swap z (σ z) * σ
      -- σ' still fixes s: σ fixes s by hypothesis, and swap z (σ z) fixes s
      -- because z, σ z ∉ s (a transposition fixes every point it does not swap).
      have hσ'fix : ∀ c ∈ (s : Set α), σ' • c = c := fun c hc ↦ by
        have hcmem := Finset.mem_coe.mp hc
        simp only [σ', mul_smul, hσ c hc,
          swap_smul_eq_of_not_mem (s := (s : Set α)) hz_not_s hb_not_s c hc]
      -- movedFinset σ' ⊆ movedFinset σ and z ∉ movedFinset σ',
      -- so the cardinality drops, and the IH applies.

      -- every atom moved by σ' = swap z (σ z) * σ is also moved by σ.
      have hsubset : movedFinset σ' ⊆ movedFinset σ := movedFinset_swap_smul_subset hmoved
      -- σ' fixes z, because σ' z = swap z (σ z) (σ z) = z (the swap sends σ z back to z).
      have hz_not_moved' : z ∉ movedFinset σ' := not_mem_movedFinset_swap_smul σ z
      have hcard' : (movedFinset σ').card < n := by
        have hlt : (movedFinset σ').card < (movedFinset σ).card :=
          Finset.card_lt_card ⟨hsubset, fun h ↦ hz_not_moved' (h hz)⟩
        omega
      -- By IH, σ' fixes x.
      have hσ'x : σ' • x = x :=
        ih (movedFinset σ').card hcard' σ' rfl hσ'fix
      -- Finally, recover the action of σ from that of σ' and swap z (σ z).
      -- Since swap is its own inverse, σ = swap z (σ z) * σ', so:
      --   σ • x = swap z (σ z) • (σ' • x) = swap z (σ z) • x = x.
      rw [swap_mul_cancel (σ := σ) (a := z), mul_smul, hσ'x, hswap_x]

/-- If two finite sets both support `x`, then their intersection also supports `x`. -/
theorem supports_inter {A₁ A₂ : Finset α} {x : X} (h₁ : supports A₁ x) (h₂ : supports A₂ x) : supports (A₁ ∩ A₂) x := by
  rw [supports_iff_swap]
  intro a a' ha ha'
  simp only [Finset.mem_inter, not_and_or] at ha ha'
  by_cases heq : a = a'
  · subst heq
    rw [swap_self, one_smul]
  · pick_new a'' (A₁ ∪ A₂ ∪ {a, a'})
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at a''New
    obtain ⟨⟨ha''₁, ha''₂⟩, ha''a, ha''a'⟩ := a''New
    have hid : swap a a' = swap a a'' * swap a' a'' * swap a a'' :=
      swap_triple_factorization heq (Ne.symm ha''a) (Ne.symm ha''a')
    have fix_a_a'' : swap a a'' • x = x := by
      rcases ha with ha | ha
      · exact (supports_iff_swap.mp h₁) a a'' ha (by simpa using ha''₁)
      · exact (supports_iff_swap.mp h₂) a a'' ha (by simpa using ha''₂)
    have fix_a'_a'' : swap a' a'' • x = x := by
      rcases ha' with ha' | ha'
      · exact (supports_iff_swap.mp h₁) a' a'' ha' (by simpa using ha''₁)
      · exact (supports_iff_swap.mp h₂) a' a'' ha' (by simpa using ha''₂)
    rw [hid, mul_smul, mul_smul, fix_a_a'', fix_a'_a'', fix_a_a'']

/-- If `s` supports `x`, then `π • s` supports `π • x`. -/
@[grind .] theorem supports_smul (π : FinitePerm α) {s : Finset α} {x : X} (hs : supports s x) : supports (π • s) (π • x) := by
  intro σ hσ
  have hx : (π⁻¹ * σ * π) • x = x := hs _ (conj_fixes_of_smul_fixes hσ)
  calc σ • (π • x)
      = π • ((π⁻¹ * σ * π) • x) := by simp [mul_smul]
    _ = π • x                    := by rw [hx]

/-- The empty set supports `x` if and only if every finite permutation fixes `x`. -/
theorem supports_empty_iff {x : X} : supports (∅ : Finset α) x ↔ ∀ π : FinitePerm α, π • x = x := by
  constructor
  · intro hs π; exact hs π (fun _ h ↦ by simp at h)
  · intro h π _; exact h π

/-- If `s` supports `x` and `t` supports `y`, then `s ∪ t` supports `(x, y)`. -/
theorem supports_prod {s t : Finset α} {x : X} {y : Y} (hs : supports s x) (ht : supports t y) :
  supports (s ∪ t) (x, y) := fun π hπ ↦ by
  simp [supports_mono Finset.subset_union_left hs π hπ,
        supports_mono Finset.subset_union_right ht π hπ]

/-- If `s` supports `x` and `a`, `b` are both outside `s`, then `swap a b` fixes `x`.
This is the Finset-membership version of `swap_smul_eq_of_not_mem`. -/
@[simp]
theorem swap_smul_eq_of_supports {s : Finset α} {x : X} (hs : supports s x) {a b : α} (ha : a ∉ s) (hb : b ∉ s) : swap a b • x = x :=
  (supports_iff_swap.mp hs) a b ha hb

/-- If `s` supports `x`, then so does `s ∪ t`. -/
theorem supports_union_left {s t : Finset α} {x : X} (hs : supports s x) : supports (s ∪ t) x :=
  supports_mono Finset.subset_union_left hs

/-- If `t` supports `x`, then so does `s ∪ t`. -/
theorem supports_union_right {s t : Finset α} {x : X} (ht : supports t x) : supports (s ∪ t) x :=
  supports_mono Finset.subset_union_right ht

/-- Equivariance iff: `s` supports `x` iff `π • s` supports `π • x`. -/
theorem supports_smul_iff (π : FinitePerm α) {s : Finset α} {x : X} : supports (π • s) (π • x) ↔ supports s x := by
  constructor
  · intro h
    have := supports_smul π⁻¹ h
    rwa [PermType.inv_smul_smul, PermType.inv_smul_smul] at this
  · exact supports_smul π

/-- `supports` is an equivariant relation: `supports (π • s) (π • x) ↔ supports s x`. -/
theorem equivariantRel_supports : EquivariantRel α (supports : Finset α → X → Prop) where
  smul_iff π _ _ := supports_smul_iff π

/-- An atom `a` is supported by the singleton `{a}`. -/
theorem supports_atom (a : α) : supports ({a} : Finset α) (a : α) := fun π h ↦ by
  simpa using h (by simp)

/-- A swap `swap a b` is supported by `{a, b}`. -/
theorem supports_swap_pair (a b : α) : supports ({a, b} : Finset α) (swap a b) := by
  rw [supports_iff_swap]
  intro c d hc hd
  rw [conj_smul, swap_inv]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc hd
  exact swap_conj_eq_of_fixed
    (by simp [swap_apply_of_ne' hc.1 hc.2])
    (by simp [swap_apply_of_ne' hd.1 hd.2])

/-! ### Equivariant functions and support -/

/-- An equivariant function preserves supports: if `s` supports `x`, then `s` supports `f x`. -/
theorem IsEquivariant.supports_image {f : X → Y} (hf : IsEquivariant α f) {s : Finset α} {x : X}
    (hs : supports s x) : supports s (f x) :=
  fun π hπ ↦ by rw [← hf.map_smul, hs π hπ]

/-- An injective equivariant function reflects supports: if `s` supports `f x`, then `s` supports `x`. -/
theorem IsEquivariant.supports_of_image {f : X → Y} (hf : IsEquivariant α f) (hinj : Function.Injective f) {s : Finset α} {x : X}
    (hs : supports s (f x)) : supports s x :=
  fun π hπ ↦ hinj (by rw [hf.map_smul]; exact hs π hπ)

/-- For an injective equivariant function, `s` supports `f x` iff `s` supports `x`. -/
theorem IsEquivariant.supports_image_iff {f : X → Y} (hf : IsEquivariant α f) (hinj : Function.Injective f) {s : Finset α} {x : X} :
    supports s (f x) ↔ supports s x :=
  ⟨hf.supports_of_image hinj, hf.supports_image⟩

/-! ### Projection support lemmas -/

/-- If `s` supports `(x, y)`, then `s` supports `x`. -/
theorem supports_fst {s : Finset α} {x : X} {y : Y} (h : supports s (x, y)) : supports s x :=
  isEquivariant_fst.supports_image h

/-- If `s` supports `(x, y)`, then `s` supports `y`. -/
theorem supports_snd {s : Finset α} {x : X} {y : Y} (h : supports s (x, y)) : supports s y :=
  isEquivariant_snd.supports_image h

/-- `supports s (x, y)` is equivalent to `supports s x ∧ supports s y`. -/
theorem supports_prod_iff {s : Finset α} {x : X} {y : Y} : supports s (x, y) ↔ supports s x ∧ supports s y :=
  ⟨fun h ↦ ⟨supports_fst h, supports_snd h⟩, fun ⟨hx, hy⟩ ↦ Finset.union_self s ▸ supports_prod hx hy⟩

/-- A binary equivariant function preserves supports: if `s` supports `x` and `s` supports `y`,
then `s` supports `f x y`. -/
theorem IsEquivariant₂.supports_image {Z : Type*} [PermType α Z] {f : X → Y → Z} (hf : IsEquivariant₂ α f) {s : Finset α} {x : X} {y : Y}
    (hx : supports s x) (hy : supports s y) : supports s (f x y) :=
  hf.curry.supports_image (supports_prod_iff.mpr ⟨hx, hy⟩)

/-! ### Sum support lemmas -/

/-- If `s` supports `x`, then `s` supports `Sum.inl x`. -/
theorem supports_inl {s : Finset α} {x : X} (hs : supports s x) : supports s (Sum.inl x : X ⊕ Y) :=
  isEquivariant_inl.supports_image hs

/-- If `s` supports `y`, then `s` supports `Sum.inr y`. -/
theorem supports_inr {s : Finset α} {y : Y} (hs : supports s y) : supports s (Sum.inr y : X ⊕ Y) :=
  isEquivariant_inr.supports_image hs

/-- If `s` supports `Sum.inl x`, then `s` supports `x`. -/
theorem supports_of_inl {s : Finset α} {x : X} (h : supports s (Sum.inl x : X ⊕ Y)) : supports s x :=
  isEquivariant_inl.supports_of_image Sum.inl_injective h

/-- If `s` supports `Sum.inr y`, then `s` supports `y`. -/
theorem supports_of_inr {s : Finset α} {y : Y} (h : supports s (Sum.inr y : X ⊕ Y)) : supports s y :=
  isEquivariant_inr.supports_of_image Sum.inr_injective h

/-- `s` supports `Sum.inl x` iff `s` supports `x`. -/
@[simp] theorem supports_inl_iff {s : Finset α} {x : X} : supports s (Sum.inl x : X ⊕ Y) ↔ supports s x :=
  isEquivariant_inl.supports_image_iff Sum.inl_injective

/-- `s` supports `Sum.inr y` iff `s` supports `y`. -/
@[simp] theorem supports_inr_iff {s : Finset α} {y : Y} : supports s (Sum.inr y : X ⊕ Y) ↔ supports s y :=
  isEquivariant_inr.supports_image_iff Sum.inr_injective

/-! ### Option support lemmas -/

/-- The empty set supports `none`. -/
theorem supports_none : supports (∅ : Finset α) (none : Option X) :=
  fun _ _ ↦ rfl

/-- If `s` supports `x`, then `s` supports `some x`. -/
theorem supports_some {s : Finset α} {x : X} (hs : supports s x) : supports s (some x : Option X) :=
  isEquivariant_some.supports_image hs

/-- If `s` supports `some x`, then `s` supports `x`. -/
theorem supports_of_some {s : Finset α} {x : X} (h : supports s (some x : Option X)) : supports s x :=
  isEquivariant_some.supports_of_image (Option.some_injective _) h

/-- `s` supports `some x` iff `s` supports `x`. -/
@[simp] theorem supports_some_iff {s : Finset α} {x : X} : supports s (some x : Option X) ↔ supports s x :=
  isEquivariant_some.supports_image_iff (Option.some_injective _)

/-! ### Atom support characterisation -/

/-- `{a}` supports an atom `b` if and only if `b = a`. -/
theorem supports_singleton_atom_iff {a b : α} : supports ({a} : Finset α) (b : α) ↔ b = a := by
  constructor
  · intro h
    by_contra hab
    pick_new c ({a, b} : Finset α)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at cNew
    have := (supports_iff_swap.mp h) b c
      (by simp only [Finset.mem_singleton]; exact hab) (by simp only [Finset.mem_singleton]; exact cNew.1)
    simp only [PermType.atoms_smul, swap_apply_left'] at this
    exact cNew.2 this
  · rintro rfl; exact supports_atom b

/-! ### Finset self-support -/

/-- A finset `s : Finset α` is supported by itself. -/
theorem supports_finset_self (s : Finset α) : supports s s := by
  intro π hfix
  ext a
  simp only [PermType.finset_smul, Finset.mem_image]
  constructor
  · rintro ⟨b, hb, rfl⟩
    have : (π : α → α) b = b := by
      simpa [PermType.atoms_smul] using hfix (Finset.mem_coe.mpr hb)
    rwa [this]
  · intro ha
    exact ⟨a, ha, by simpa [PermType.atoms_smul] using hfix (Finset.mem_coe.mpr ha)⟩

/-! ### Removing an unnecessary support atom -/

/-- If `s` supports `x` and every swap of `a` with an atom outside `s` fixes `x`,
then `s.erase a` still supports `x`. -/
theorem supports_erase_of_swap_fix {s : Finset α} {x : X} {a : α} (hs : supports s x) (ha : ∀ b, b ∉ s → swap a b • x = x) :
    supports (s.erase a) x := by
  rw [supports_iff_swap]
  intro c d hc hd
  simp only [Finset.mem_erase, not_and_or, ne_eq, not_not] at hc hd
  rcases hc with rfl | hc <;> rcases hd with rfl | hd
  · rw [swap_self, one_smul]
  · exact ha d hd
  · rw [swap_comm]; exact ha c hc
  · exact swap_smul_eq_of_supports hs hc hd

/-! ### Support when both permutation and element are supported -/

/-- If `s` supports both `x` and `π`, then `s` supports `π • x`. -/
theorem supports_smul_of_supports_both {s : Finset α} {x : X} {π : FinitePerm α} (hx : supports s x) (hπ : supports s π) :
    supports s (π • x) :=
  isEquivariant₂_smul.supports_image hπ hx

end SwapChar

/-! ## FinSupported API -/

section FinSupportedAPI

open PermType

variable {α : Type*} [Name α] {X : Type*} [PermType α X] {Y : Type*} [PermType α Y]

/-- If `x` is finitely supported, then `π • x` is finitely supported. -/
theorem FinSupported.smul {x : X} (h : FinSupported x) (π : FinitePerm α) : FinSupported (π • x) :=
  let ⟨s, hs⟩ := h; ⟨π • s, supports_smul π hs⟩

/-- If `x` and `y` are finitely supported, then `(x, y)` is finitely supported. -/
theorem FinSupported.prod {x : X} {y : Y} (hx : FinSupported x) (hy : FinSupported y) : FinSupported (x, y) :=
  let ⟨s, hs⟩ := hx; let ⟨t, ht⟩ := hy; ⟨s ∪ t, supports_prod hs ht⟩

/-- If `(x, y)` is finitely supported, then `x` is finitely supported. -/
theorem FinSupported.fst {x : X} {y : Y} (h : FinSupported (x, y)) : FinSupported x :=
  let ⟨s, hs⟩ := h; ⟨s, supports_fst hs⟩

/-- If `(x, y)` is finitely supported, then `y` is finitely supported. -/
theorem FinSupported.snd {x : X} {y : Y} (h : FinSupported (x, y)) : FinSupported y :=
  let ⟨s, hs⟩ := h; ⟨s, supports_snd hs⟩

/-- If `x` is finitely supported, then `Sum.inl x` is finitely supported. -/
theorem FinSupported.inl {x : X} (h : FinSupported x) : FinSupported (Sum.inl x : X ⊕ Y) :=
  let ⟨s, hs⟩ := h; ⟨s, supports_inl hs⟩

/-- If `y` is finitely supported, then `Sum.inr y` is finitely supported. -/
theorem FinSupported.inr {y : Y} (h : FinSupported y) : FinSupported (Sum.inr y : X ⊕ Y) :=
  let ⟨s, hs⟩ := h; ⟨s, supports_inr hs⟩

/-- `some x` is finitely supported if `x` is. -/
theorem FinSupported.some {x : X} (h : FinSupported x) : FinSupported (some x : Option X) :=
  let ⟨s, hs⟩ := h; ⟨s, supports_some hs⟩

/-- `none` is finitely supported. -/
theorem FinSupported.none : FinSupported (none : Option X) := ⟨∅, supports_none⟩

/-! ### FinSupported reverses -/

/-- If `Sum.inl x` is finitely supported, then `x` is finitely supported. -/
theorem FinSupported.of_inl {x : X} (h : FinSupported (Sum.inl x : X ⊕ Y)) : FinSupported x :=
  let ⟨s, hs⟩ := h; ⟨s, supports_of_inl hs⟩

/-- If `Sum.inr y` is finitely supported, then `y` is finitely supported. -/
theorem FinSupported.of_inr {y : Y} (h : FinSupported (Sum.inr y : X ⊕ Y)) : FinSupported y :=
  let ⟨s, hs⟩ := h; ⟨s, supports_of_inr hs⟩

/-- If `some x` is finitely supported, then `x` is finitely supported. -/
theorem FinSupported.of_some {x : X} (h : FinSupported (Option.some x : Option X)) : FinSupported x :=
  let ⟨s, hs⟩ := h; ⟨s, supports_of_some hs⟩

/-! ### FinSupported iff-variants -/

/-- `(x, y)` is finitely supported iff both `x` and `y` are. -/
theorem finSupported_prod_iff {x : X} {y : Y} : FinSupported (x, y) ↔ FinSupported x ∧ FinSupported y :=
  ⟨fun h ↦ ⟨h.fst, h.snd⟩, fun ⟨hx, hy⟩ ↦ hx.prod hy⟩

/-- `Sum.inl x` is finitely supported iff `x` is. -/
theorem finSupported_inl_iff {x : X} : FinSupported (Sum.inl x : X ⊕ Y) ↔ FinSupported x :=
  ⟨FinSupported.of_inl, FinSupported.inl⟩

/-- `Sum.inr y` is finitely supported iff `y` is. -/
theorem finSupported_inr_iff {y : Y} : FinSupported (Sum.inr y : X ⊕ Y) ↔ FinSupported y :=
  ⟨FinSupported.of_inr, FinSupported.inr⟩

/-- `some x` is finitely supported iff `x` is. -/
theorem finSupported_some_iff {x : X} : FinSupported (Option.some x : Option X) ↔ FinSupported x :=
  ⟨FinSupported.of_some, FinSupported.some⟩

/-! ### FinSupported for concrete values -/

/-- An atom `a` is always finitely supported (by `{a}`). -/
theorem FinSupported.atom (a : α) : FinSupported (α := α) (X := α) a :=
  ⟨{a}, supports_atom a⟩

/-- A swap `swap a b` is always finitely supported (by `{a, b}`). -/
theorem FinSupported.swap (a b : α) : FinSupported (swap a b) :=
  ⟨{a, b}, supports_swap_pair a b⟩

/-! ### Equivariant functions and FinSupported -/

/-- An equivariant image of a finitely supported element is finitely supported. -/
theorem IsEquivariant.finSupported {f : X → Y} (hf : IsEquivariant α f) {x : X} (h : FinSupported x) : FinSupported (f x) :=
  let ⟨s, hs⟩ := h; ⟨s, hf.supports_image hs⟩

/-- An injective equivariant function reflects finite support. -/
theorem IsEquivariant.finSupported_of_image {f : X → Y} (hf : IsEquivariant α f) (hinj : Function.Injective f) {x : X}
    (h : FinSupported (f x)) : FinSupported x :=
  let ⟨s, hs⟩ := h; ⟨s, hf.supports_of_image hinj hs⟩

/-- For an injective equivariant function, `f x` is finitely supported iff `x` is. -/
theorem IsEquivariant.finSupported_iff {f : X → Y} (hf : IsEquivariant α f) (hinj : Function.Injective f) {x : X} :
    FinSupported (f x) ↔ FinSupported x :=
  ⟨hf.finSupported_of_image hinj, hf.finSupported⟩

/-- A binary equivariant function preserves finite support. -/
theorem IsEquivariant₂.finSupported {Z : Type*} [PermType α Z] {f : X → Y → Z} (hf : IsEquivariant₂ α f) {x : X} {y : Y}
    (hx : FinSupported x) (hy : FinSupported y) : FinSupported (f x y) :=
  hf.curry.finSupported (hx.prod hy)

/-! ### Equivariance of FinSupported -/

/-- `FinSupported` is an equivariant predicate. -/
theorem equivariantPred_finSupported : EquivariantPred α (FinSupported (α := α) (X := X)) := by
  intros π x
  exact
    ⟨fun ⟨s, hs⟩ ↦ by
      rw [← PermType.inv_smul_smul π x]
      exact ⟨π⁻¹ • s, supports_smul π⁻¹ hs⟩, fun h ↦ h.smul π⟩

/-- If `π • x` is finitely supported, then `x` is finitely supported. -/
theorem FinSupported.of_smul {x : X} {π : FinitePerm α} (h : FinSupported (π • x)) : FinSupported x :=
  equivariantPred_finSupported.of_smul π h

/-- `π • x` is finitely supported iff `x` is. -/
theorem finSupported_smul_iff {x : X} {π : FinitePerm α} : FinSupported (π • x) ↔ FinSupported x :=
  equivariantPred_finSupported.smul_iff' π x

end FinSupportedAPI

end NominalSets
