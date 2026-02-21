import NominalSets.Swap

import Mathlib.GroupTheory.GroupAction.Support
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Card

/-!
# Support and the Swap Characterisation

This file introduces the `supports` relation and `FinSupported` predicate, and proves
the key theorems about them.

The central result is the swap characterisation of supports (Pitts, Prop. 2.1): a finite
set `s` supports `x` if and only if every transposition of two atoms outside `s` fixes `x`.
The proof uses the `swap` and `movedFinset` machinery from `NominalSets.Swap` and
`NominalSets.PermType` via strong induction on the number of moved points.

## Main definitions

* `supports s x` — thin abbreviation for `MulAction.Supports (FinitePerm α) ↑s x`
  (where `s : Finset α`), specialising the acting group to `FinitePerm α`.
* `FinSupported x` — `x` is supported by some finite set of atoms.

## Main results

* `supports_iff_swap` — **Pitts, Prop. 2.1**: `s` supports `x` iff every transposition
  of two atoms outside `s` fixes `x`.
* `supports_inter` — the intersection of two finite supports is again a support.
* `supports_smul` — if `s` supports `x`, then `π • s` supports `π • x`.

## References

* [A. M. Pitts, *Nominal Sets*][Pitts2013], Chapter 2.
-/

section Support

open MulAction

variable {α : Type*} [Name α]

/-- `s` supports `b` with respect to the group `FinitePerm α`.
A thin abbreviation over `MulAction.Supports` that fixes the acting group to `FinitePerm α`
and restricts the support set to a `Finset α`. -/
abbrev supports {β : Type*} [MulAction (FinitePerm α) β] (s : Finset α) (b : β) : Prop :=
  Supports (FinitePerm α) (s : Set α) b

/-- An element `x : X` is **finitely supported** if there exists a finite set of atoms
`s : Finset α` such that every finite permutation fixing `s` pointwise also fixes `x`. -/
def FinSupported {X : Type*} [PermType α X] (x : X) : Prop :=
  ∃ s : Finset α, supports s x

end Support

/-! ## Proposition 2.1 and the intersection of supports -/

section SwapChar

open MulAction PermType

variable {α : Type*} [Name α] {X : Type*} [PermType α X]

/-- **Pitts, Prop. 2.1.** A finset `s` supports `x` under `FinitePerm α` if and only if
every transposition of two atoms *outside* `s` fixes `x`. -/
theorem supports_iff_swap {s : Finset α} {x : X} :
    supports s x ↔ ∀ a₁ a₂ : α, a₁ ∉ s → a₂ ∉ s → swap a₁ a₂ • x = x := by
  constructor
  -- (→) if s supports x and a₁, a₂ ∉ s, then swap a₁ a₂ fixes s
  -- (it only moves a₁ and a₂, which are outside s), so the support
  -- condition gives swap a₁ a₂ • x = x directly.
  · intro hs a₁ a₂ ha₁ ha₂
    apply hs
    intro c hcs
    simp only [PermType.atoms_smul]
    exact Equiv.swap_apply_of_ne_of_ne (fun h ↦ ha₁ (h ▸ Finset.mem_coe.mp hcs))
                                       (fun h ↦ ha₂ (h ▸ Finset.mem_coe.mp hcs))
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
        have := hσ (σ z) (Finset.mem_coe.mpr hin); simp only [PermType.atoms_smul] at this
        exact hmoved (σ.val.injective this)
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
          swapFP_fixes_of_not_mem (s := (s : Set α)) hz_not_s hb_not_s c hc]
      -- movedFinset σ' ⊆ movedFinset σ and z ∉ movedFinset σ',
      -- so the cardinality drops, and the IH applies.

      -- every atom moved by σ' = swap z (σ z) * σ is also moved by σ.
      have hsubset : movedFinset σ' ⊆ movedFinset σ := movedFinset_swap_smul_subset hmoved
      -- σ' fixes z, because σ' z = swap z (σ z) (σ z) = z (the swap sends σ z back to z).
      have hz_not_moved' : z ∉ movedFinset σ' := not_mem_movedFinset_swap_smul
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
theorem supports_inter (A₁ A₂ : Finset α) (x : X)
    (h₁ : supports A₁ x) (h₂ : supports A₂ x) :
    supports (A₁ ∩ A₂) x := by
  rw [supports_iff_swap]
  intro a a' ha ha'
  simp only [Finset.mem_inter, not_and_or] at ha ha'
  by_cases heq : a = a'
  · subst heq
    rw [swap_self, one_smul]
  · pick_new a'' (A₁ ∪ A₂ ∪ {a, a'})
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at ha''
    obtain ⟨⟨ha''₁, ha''₂⟩, ha''a, ha''a'⟩ := ha''
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
theorem supports_smul (π : FinitePerm α) {s : Finset α} {x : X}
    (hs : supports s x) :
    supports (π • s) (π • x) := by
  intro σ hσ
  -- Key: show π⁻¹ * σ * π fixes every b ∈ s
  have hconj : ∀ b ∈ (s : Set α), (π⁻¹ * σ * π) • b = b := fun b hb ↦ by
    -- π • b ∈ π • s (since π⁻¹ • (π • b) = b ∈ s)
    have hpib : π • b ∈ π • s := by
      simp only [PermType.mem_smul_finset_iff, PermType.inv_smul_smul]
      exact Finset.mem_coe.mp hb
    -- σ fixes π • b
    have hfix : σ • (π • b) = π • b := hσ (Finset.mem_coe.mpr hpib)
    -- (π⁻¹ * σ * π) • b = π⁻¹ • (σ • (π • b)) = b
    simp only [mul_smul, hfix, PermType.inv_smul_smul]
  -- π⁻¹ * σ * π fixes x by the support condition
  have hx : (π⁻¹ * σ * π) • x = x := hs _ hconj
  -- σ • (π • x) = π • ((π⁻¹ * σ * π) • x) = π • x
  calc σ • (π • x)
      = π • (π⁻¹ • (σ • (π • x))) := (PermType.smul_inv_smul π _).symm
    _ = π • ((π⁻¹ * σ * π) • x)   := by rw [mul_smul, mul_smul]
    _ = π • x                      := by rw [hx]

end SwapChar
