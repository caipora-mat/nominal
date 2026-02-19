import NominalSets.Wheels
import NominalSets.Name
import NominalSets.FinitePerm.Basic

import Mathlib.GroupTheory.GroupAction.Support
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Equiv.Basic

/-!
# Permutation Types

A **name permutation type** (also called a *nominal set without the finite-support condition*,
or a *Perm-set*) is a type `X` equipped with an action of the group `FinitePerm α` of
finite permutations of a name type `α`.

Formally this is just a `MulAction (FinitePerm α) X`, but we introduce the typeclass
`PermType` to:

1. Give a convenient single bundled constraint for the nominal-sets library.
2. Provide a uniform `•` notation via the existing `MulAction` infrastructure.
3. Collect basic instances (atoms, products, function spaces) in one place.

## Main definitions

* `PermType α X` — typeclass asserting that `X` carries a `FinitePerm α`-action.
* `PFun α X Y` — newtype wrapper for `X → Y` carrying the conjugation action
  `(π • f) x = π • f (π⁻¹ • x)`, avoiding a diamond with Mathlib's `Pi.instSMul`.
* `supports s x` — abbreviation for `MulAction.Supports (FinitePerm α) s x`.
* `FinSupported x` — `x` is supported by some finite set of atoms.
* `swap a b` — the transposition of `a` and `b` as a bundled `FinitePerm α`.
* `movedFinset π` — the finite set of atoms moved by `π`.

## Instances

* `PermType.instAtoms` — atoms `α` act on themselves by direct application (`π • a = π a`).
* `PermType.instProd` — component-wise action on `X × Y` (`π • (x, y) = (π • x, π • y)`).
* `PFun.instPermType` — conjugation action on `PFun α X Y` (`(π • f) x = π • f (π⁻¹ • x)`).

## Main results

* `PermType.smul_eq_iff_eq_inv_smul` — `π • x = y ↔ x = π⁻¹ • y`.
* `PermType.smul_injective` — the action of any permutation is injective.
* `supports_iff_swap` — **Pitts, Prop. 2.1**: `s` supports `x` iff every transposition
  of two atoms outside `s` fixes `x`.
* `supports_inter` — the intersection of two finite supports is again a support.

## Notation

We inherit `•` from `MulAction`. Given `π : FinitePerm α` and `x : X`, write `π • x`.

## References

* [A. M. Pitts, *Nominal Sets*][Pitts2013], Chapter 1.
-/

/-- A **permutation type** is a type `X` equipped with an action of the group
`FinitePerm α` of finite permutations. This is a thin wrapper around
`MulAction (FinitePerm α) X` that gives a convenient single typeclass -/
class PermType (α : Type*) [Name α] (X : Type*) extends MulAction (FinitePerm α) X

variable {α : Type*} [Name α]

namespace PermType

/-! ### Canonical action on atoms -/

/-- The atoms `α` form a permutation type: a finite permutation acts on `α` by
direct application, i.e., `π • a = π a`. -/
instance instAtoms : PermType α α where
  smul π a := π a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp, grind =]
theorem atoms_smul (π : FinitePerm α) (a : α) : (π • a : α) = π a := rfl

/-! ### Product -/

/-- The Cartesian product of two permutation types is a permutation type,
with the component-wise action `π • (x, y) = (π • x, π • y)`. -/
instance instProd {X Y : Type*} [PermType α X] [PermType α Y] :
    PermType α (X × Y) where
  smul π p := (π • p.1, π • p.2)
  one_smul p := by simp
  mul_smul π σ p := by simp [mul_smul]

@[simp, grind =]
theorem prod_smul (X Y : Type*) [PermType α X] [PermType α Y]
    (π : FinitePerm α) (x : X) (y : Y) : π • (x, y) = (π • x, π • y) := rfl

/-! ### Function space

#### The diamond problem

The permutation action on `X → Y` is:

  `(π • f) x = π • f (π⁻¹ • x)`

However, Mathlib already provides `Pi.instSMul`, which gives a *pointwise* action on
any `ι → α` whenever `SMul M α`:

  `(π • f) x = π • f x`   -- Pi.instSMul

Because `PermType α (X → Y)` extends `MulAction (FinitePerm α) (X → Y)`, which in turn
gives a `SMul (FinitePerm α) (X → Y)`, both instances become available for `X → Y`.
Lean's instance search then faces a **diamond**: it may synthesise `Pi.instSMul` before
`instFun`, yielding the wrong action.

To avoid this conflict entirely, the action is wrapped in the newtype `PFun α X Y`
(a transparent copy of `X → Y`) rather than being placed on the bare function type.
The old instance `instFun` is kept below for reference and for use in proofs that
explicitly request it.
-/

/-- `PFun α X Y` is a **newtype wrapper** around `X → Y` carrying the action
`(π • f) x = π • f (π⁻¹ • x)`.

The wrapper is needed because Mathlib's `Pi.instSMul` already equips the type
`X → Y` with a *pointwise* action `(π • f) x = π • f x`, causing a diamond when
we try to register the action directly on `X → Y`. -/
def PFun (α : Type*) [Name α] (X Y : Type*) := X → Y

namespace PFun

/-- Coerce a plain function into a `PFun`. -/
instance instCoe {X Y : Type*} : Coe (X → Y) (PFun α X Y) := ⟨id⟩

/-- Apply a `PFun` to an argument. -/
instance instFunLike {X Y : Type*} : FunLike (PFun α X Y) X Y where
  coe f := f
  coe_injective' _ _ h := h

@[simp] theorem coe_apply {X Y : Type*} (f : X → Y) (x : X) : (f : PFun α X Y) x = f x := rfl

/-- The action on `PFun α X Y`: `(π • f) x = π • f (π⁻¹ • x)`. -/
instance instPermType {X Y : Type*} [PermType α X] [PermType α Y] :
    PermType α (PFun α X Y) where
  smul π f x := π • f (π⁻¹ • x)
  one_smul f := by
    funext x
    change (1 : FinitePerm α) • f (1⁻¹ • x) = f x
    simp [one_smul]
  mul_smul π σ f := by
    funext x
    change (π * σ) • f ((π * σ)⁻¹ • x) = π • σ • f (σ⁻¹ • π⁻¹ • x)
    rw [mul_inv_rev, mul_smul, mul_smul]

@[simp, grind =]
theorem smul_apply {X Y : Type*} [PermType α X] [PermType α Y]
    (π : FinitePerm α) (f : PFun α X Y) (x : X) : (π • f) x = π • f (π⁻¹ • x) := rfl

end PFun

/-! #### PROBLEM: action directly on `X → Y`

The instance below equips the bare function type with an action.
It is **not** registered as a global `PermType` instance to avoid the diamond
with `Pi.instSMul`; use `PFun` instead. It is kept here for documentation -/

/- action on `X → Y` (not a global instance; see `PFun`). -/
-- def funPermType {X Y : Type*} [PermType α X] [PermType α Y] :
--     PermType α (X → Y) where
--   smul π f x := π • f (π⁻¹ • x)
--   one_smul f := by
--     funext x
--     change (1 : FinitePerm α) • f (1⁻¹ • x) = f x
--     simp [one_smul]
--   mul_smul π σ f := by
--     funext x
--     change (π * σ) • f ((π * σ)⁻¹ • x) = π • σ • f (σ⁻¹ • π⁻¹ • x)
--     rw [mul_inv_rev, mul_smul, mul_smul]

-- Note: Mathlib's `Pi.instSMul` (pointwise action) conflicts with the conjugation
-- action defined in `instFun`. We state `fun_smul` using `@SMul.smul _ _ instFun.toSMul`
-- to pin the right instance, avoiding the ambiguity.
-- @[simp]
-- theorem fun_smul {X Y : Type*} [PermType α X] [PermType α Y]
--     (π : FinitePerm α) (f : X → Y) (x : X) :
--     @SMul.smul _ _ instFun.toSMul π f x = π • f (π⁻¹ • x) := rfl

/-! ### Basic lemmas -/

section

variable {X : Type*} [PermType α X]

/-- The action of the identity permutation is trivial. -/
@[simp, grind =]
theorem one_smul' (x : X) : (1 : FinitePerm α) • x = x :=
  one_smul _ x

/-- The action is compatible with multiplication in `FinitePerm α`. -/
@[grind =, grind =_]
theorem mul_smul' (π σ : FinitePerm α) (x : X) : (π * σ) • x = π • σ • x :=
  mul_smul π σ x

/-- Applying a permutation and then its inverse recovers the original element. -/
@[simp, grind =, grind! .]
theorem inv_smul_smul (π : FinitePerm α) (x : X) : π⁻¹ • π • x = x := by
  rw [← mul_smul, inv_mul_cancel, one_smul]

/-- Applying a permutation after its inverse recovers the original element. -/
@[simp, grind =, grind! .]
theorem smul_inv_smul (π : FinitePerm α) (x : X) : π • π⁻¹ • x = x := by
  rw [← mul_smul, mul_inv_cancel, one_smul]

/-- The permutation action is injective -/
@[grind .]
theorem smul_injective (π : FinitePerm α) {x y : X} (h : π • x = π • y) : x = y := by
  have := congr_arg (π⁻¹ • ·) h
  simp only [inv_smul_smul] at this
  exact this

/-- Two elements are related by the action iff they are in the same orbit. -/
@[grind .]
theorem smul_eq_iff_eq_inv_smul (π : FinitePerm α) (x y : X) :
    π • x = y ↔ x = π⁻¹ • y := by
  constructor
  · rintro rfl; simp
  · rintro rfl; simp

end

end PermType

section Support

open MulAction

variable {α : Type*} [Name α]

/-- `s` supports `b` with respect to the group `FinitePerm α`.
A thin abbreviation over `MulAction.Supports` that fixes the acting group. -/
abbrev supports {β : Type*} [MulAction (FinitePerm α) β] (s : Set α) (b : β) : Prop :=
  Supports (FinitePerm α) s b

/-- An element `x : X` is **finitely supported** if there exists a finite set of atoms
`s : Finset α` such that every finite permutation fixing `s` pointwise also fixes `x`. -/
def FinSupported {X : Type*} [PermType α X] (x : X) : Prop :=
  ∃ s : Finset α, supports (s : Set α) x

end Support

/-! ## Proposition 2.1 and the intersection of supports -/

section SwapChar

open MulAction

variable {α : Type*} [Name α] {X : Type*} [PermType α X]

/-- Bundled transposition in `FinitePerm α`. -/
def swap (a b : α) : FinitePerm α := ⟨Equiv.swap a b, FinitePerm.swap_finite a b⟩

@[simp, norm_cast]
theorem swapFP_val (a b : α) : (swap a b : FinitePerm α) = Equiv.swap a b := rfl

/-- The finite set of atoms moved by a finite permutation. -/
@[reducible]
noncomputable def movedFinset (π : FinitePerm α) : Finset α :=
  π.property.toFinset

-- TODO reorder lemma
omit [Name α] in
@[simp]
theorem mem_movedFinset {π : FinitePerm α} {a : α} :
    a ∈ movedFinset π ↔ π a ≠ a := by
  simp only [movedFinset, Set.Finite.mem_toFinset, Equiv.Perm.movedPoints, Set.mem_setOf_eq, DFunLike.coe]

/-- A transposition of atoms outside `s` fixes `s` pointwise. -/
@[simp, grind ., grind →]
theorem swapFP_fixes_of_not_mem {s : Set α} {a b : α}
    (ha : a ∉ s) (hb : b ∉ s) (c : α) (hc : c ∈ s) : (swap a b) • c = c := by
  simp only [PermType.atoms_smul]
  exact Equiv.swap_apply_of_ne_of_ne (fun h ↦ ha (h ▸ hc)) (fun h ↦ hb (h ▸ hc))

theorem swap_self (a : α) : swap a a = (1 : FinitePerm α) :=
  Subtype.ext (by simp [swapFP_val, Equiv.swap_self]; rfl)

/-- A finite permutation with no moved points is the identity. -/
theorem movedFinset_eq_empty_iff_one {σ : FinitePerm α} :
    movedFinset σ = ∅ ↔ σ = 1 := by
  constructor
  · intro h
    apply Subtype.ext
    apply Equiv.Perm.ext
    intro c
    by_contra hne
    have : c ∈ movedFinset σ := mem_movedFinset.mpr hne
    simp [h] at this
  · rintro rfl
    simp [movedFinset, Equiv.Perm.movedPoints]

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

/-- **Pitts, Prop. 2.1.** A set `s` supports `x` under `FinitePerm α` if and only if
every transposition of two atoms *outside* `s` fixes `x`. -/
theorem supports_iff_swap {s : Set α} {x : X} :
    supports s x ↔ ∀ a₁ a₂ : α, a₁ ∉ s → a₂ ∉ s → swap a₁ a₂ • x = x := by
  constructor
  -- (→) if s supports x and a₁, a₂ ∉ s, then swap a₁ a₂ fixes s
  -- (it only moves a₁ and a₂, which are outside s), so the support
  -- condition gives swap a₁ a₂ • x = x directly.
  · intro hs a₁ a₂ ha₁ ha₂
    apply hs
    intro c hcs
    simp only [PermType.atoms_smul]
    exact Equiv.swap_apply_of_ne_of_ne (fun h ↦ ha₁ (h ▸ hcs)) (fun h ↦ ha₂ (h ▸ hcs))
  -- (←) assuming every transposition of atoms outside s fixes x,
  -- show that every finite permutation σ that fixes s also fixes x.
  --
  -- Strategy: strong induction on |movedFinset σ| (π), peeling off one moved point
  -- at a time by left-multiplying by a suitable transposition.
  · intro hswap π hfix
    -- We generalise to an arbitrary σ (instead of π) so that the induction
    -- hypothesis applies to the smaller permutation σ' we construct below.
    suffices ∀ n : ℕ, ∀ σ : FinitePerm α,
        (movedFinset σ).card = n → (∀ c ∈ s, σ • c = c) → σ • x = x by
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
        have := hσ z hin
        contradiction
      have hb_not_s : σ z ∉ s := fun hin ↦ by
        have := hσ (σ z) hin; simp only [PermType.atoms_smul] at this
        exact hmoved (σ.val.injective this)
      -- Because both z and (σ z) are not in s, our hypothesis gives:
      -- swap(z, σ z) fixes x.
      have hswap_x : swap z (σ z) • x = x := hswap z (σ z) hz_not_s hb_not_s
      -- Define the "reduced" permutation σ' = swap(z, σ z) * σ.
      -- Key idea: swap(z, σ z) undoes what σ does to z, so z becomes a fixed point of σ'.
      let σ' : FinitePerm α := swap z (σ z) * σ
      -- σ' still fixes s: σ fixes s by hypothesis, and swap z (σ z) fixes s
      -- because z, σ z ∉ s (a transposition fixes every point it does not swap).
      have hσ'fix : ∀ c ∈ s, σ' • c = c := fun c hc ↦ by
        simp only [σ', mul_smul, hσ c hc, swapFP_fixes_of_not_mem hz_not_s hb_not_s c hc]
      -- movedFinset σ' ⊆ movedFinset σ and z ∉ movedFinset σ',
      -- so the cardinality drops, and the IH applies.

      -- every atom moved by σ' = swap z (σ z) * σ is also moved by σ.
      -- (If σ fixes c, then σ' c = swap z (σ z) (σ c) = swap z (σ z) c, which equals c
      -- as long as c ∉ {z, σ z}; and if c = z then σ z = z, contradicting hmoved;
      -- if c = σ z then injectivity of σ gives σ z = z, again a contradiction.)
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
    (h₁ : supports (α := α) (A₁ : Set α) x) (h₂ : supports (α := α) (A₂ : Set α) x) :
    supports (α := α) ((A₁ ∩ A₂ : Finset α) : Set α) x := by
  rw [supports_iff_swap]
  intro a a' ha ha'
  norm_cast at ha ha'
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

end SwapChar
