import Nominal.Set

/-!
# Lambda Calculus as a Nominal Set (Canonical Formulation)

This file constructs the untyped lambda calculus as a nominal set, following the
approach of Pitts (2006) and Urban (2008). The construction proceeds in four stages:

1. **Raw terms** (`LamTerm α`) — concrete syntax with explicit binder names.
2. **Alpha-equivalence** (`AEq`) — identifying terms that differ only in bound names.
3. **The quotient** (`Term α`) — alpha-equivalence classes, forming a nominal set.
4. **Public syntax interface** — constructor injectivity and disjointness,
   abstraction equality, and inversion at a chosen fresh binder.

Clients should use `Term.var`, `Term.app`, and `Term.lam` together with their
public equality and freshness lemmas. Strong induction is provided separately in
`Instances.LambdaCalculus.Induction`; ordinary syntax inversion only needs this module.

The key design choice is using `Bind α X` (a plain binder-body pair) in the `lam`
constructor instead of `NameAbs α X` (which is itself a quotient). This makes
`LamTerm` a *nested* inductive type, avoiding the need for quotient-of-quotient
constructions at the cost of some extra manual work (see §1 below).

## References

* A. M. Pitts, *Alpha-Structural Recursion and Induction*, JACM 53(3), 2006
* C. Urban, *Nominal Techniques in Isabelle/HOL*, JAR, 2008
* A. M. Pitts, *Nominal Sets*, Cambridge, 2013, Chapters 4–8
-/

namespace LambdaCalculus

open Nominal.Core Nominal.Set NameAbs

universe u

variable {α : Type u} [Name α]

/-!
## Raw syntax

A `LamTerm α` is a concrete lambda term whose binder names are drawn from the
atom type `α`. We use `Bind α X` — a simple record of a binder and a body — in
the `lam` constructor so that `LamTerm` can be a plain (nested) inductive type.

**Nested inductive caveat.** Because `LamTerm` mentions `Bind α (LamTerm α)`,
it is a *nested* inductive. This means:
- `deriving DecidableEq` fails (we define `LamTerm.decEq` manually).
- The `induction` tactic is unavailable; we use *functional induction* via
  `f.induct` instead (available since Lean 4.8).
-/

/-- A raw binder-body pair with no proof obligations.
Usable in nested inductive definitions (unlike `NameAbs`, which is a quotient). -/
structure Bind (α : Type u) (X : Type u) where
  binder : α
  body : X
  deriving DecidableEq

/-- Raw lambda calculus terms. Binder names are concrete atoms; alpha-equivalence
is handled externally via `AEq`. -/
inductive LamTerm (α : Type u) [Name α] where
  | var : α → LamTerm α
  | app : LamTerm α → LamTerm α → LamTerm α
  | lam : Bind α (LamTerm α) → LamTerm α

/-- Notation: `⌜a⌝` for `LamTerm.var a` (variable). -/
scoped notation:max "⌜" a "⌝" => LamTerm.var a

/-- Notation: `t ◃ s` for `LamTerm.app t s` (application, "s feeds into t"). -/
scoped infixl:70 " ◃ " => LamTerm.app

/-- Notation: `ƛ[a] t` for `LamTerm.lam ⟨a, t⟩` (lambda abstraction). -/
scoped notation:max "ƛ[" a "]" t:arg => LamTerm.lam (Bind.mk a t)

/-- Size of a pre-term (for well-founded recursion). -/
def LamTerm.size : LamTerm α → ℕ
  | .var _ => 0
  | .app t s => t.size + s.size + 1
  | .lam ⟨_, t⟩ => t.size + 1

/-- `DecidableEq` for `LamTerm`, defined manually because Lean's `deriving` handler
does not support nested inductive types. -/
def LamTerm.decEq : (t s : LamTerm α) → Decidable (t = s)
  | .var a, .var b =>
    if h : a = b then isTrue (h ▸ rfl)
    else isFalse (fun h' => by cases h'; exact h rfl)
  | .var _, .app _ _ => isFalse nofun
  | .var _, .lam _ => isFalse nofun
  | .app _ _, .var _ => isFalse nofun
  | .app t₁ t₂, .app s₁ s₂ =>
    match t₁.decEq s₁, t₂.decEq s₂ with
    | isTrue h₁, isTrue h₂ => isTrue (h₁ ▸ h₂ ▸ rfl)
    | isFalse h₁, _ => isFalse (fun h => by cases h; exact h₁ rfl)
    | _, isFalse h₂ => isFalse (fun h => by cases h; exact h₂ rfl)
  | .app _ _, .lam _ => isFalse nofun
  | .lam _, .var _ => isFalse nofun
  | .lam _, .app _ _ => isFalse nofun
  | .lam ⟨a, t⟩, .lam ⟨b, s⟩ =>
    if hab : a = b then
      match t.decEq s with
      | isTrue hts => isTrue (hab ▸ hts ▸ rfl)
      | isFalse hts => isFalse (fun h => by cases h; exact hts rfl)
    else isFalse (fun h => by cases h; exact hab rfl)

instance instDecidableEqLamTerm : DecidableEq (LamTerm α) := LamTerm.decEq

/-!
## Permutation action on raw terms

Permutations act on `LamTerm α` by permuting every atom — both free and bound.
This is the standard action on *raw* terms; the quotient `Term α` inherits it.

The proofs of `one_smul` and `mul_smul` use functional induction via `smul.induct`,
which is Lean's auto-generated induction principle for the recursive function `smul`.
-/

namespace LamTerm

/-- Recursive permutation action on pre-terms. -/
def smul (π : FinitePerm α) : LamTerm α → LamTerm α
  | var a     => var (π • a)
  | app t s   => app (smul π t) (smul π s)
  | lam ⟨a, t⟩ => lam ⟨π • a, smul π t⟩

instance : SMul (FinitePerm α) (LamTerm α) where smul := smul

@[simp] theorem smul_var (π : FinitePerm α) (a : α) : π • ⌜a⌝ = ⌜π • a⌝ := rfl
@[simp] theorem smul_app (π : FinitePerm α) (t s : LamTerm α) : π • (t ◃ s) = (π • t) ◃ (π • s) := rfl
@[simp] theorem smul_lam (π : FinitePerm α) (a : α) (t : LamTerm α) : π • ƛ[a]t = ƛ[π • a](π • t) := rfl

private theorem one_smul' (t : LamTerm α) : (1 : FinitePerm α) • t = t := by
  induction t using smul.induct (α := α) with
  | case1 a => simp                       -- var
  | case2 t s iht ihs => simp [iht, ihs]  -- app
  | case3 a t iht => simp [iht]           -- lam

private theorem mul_smul' (π σ : FinitePerm α) (t : LamTerm α) :
    (π * σ) • t = π • (σ • t) := by
  induction t using smul.induct (α := α) with
  | case1 a => simp [mul_smul]             -- var
  | case2 t s iht ihs => simp [iht, ihs]   -- app
  | case3 a t iht => simp [mul_smul, iht]  -- lam

instance : MulAction (FinitePerm α) (LamTerm α) where
  one_smul := one_smul'
  mul_smul := mul_smul'

instance instPermType : PermType α (LamTerm α) where
  __ := (inferInstance : MulAction (FinitePerm α) (LamTerm α))

@[simp] theorem size_smul (π : FinitePerm α) (t : LamTerm α) : (π • t).size = t.size := by
  induction t using smul.induct (α := α) with
  | case1 a => simp [size]                      -- var
  | case2 t s iht ihs => simp [size, iht, ihs]  -- app
  | case3 a t iht => simp [size, iht]           -- lam

/-!
## Names and free variables

Two notions of "the atoms in a term":

- `names t` — *all* atoms (free and bound). This is the support of the *raw* term.
- `fv t` — *free* variables only. This will be the support of the *quotient* term.

Both are equivariant: `names (π • t) = π • names t` and likewise for `fv`. The
inclusion `fv t ⊆ names t` holds because every free variable is also a name.
-/

/-- All atoms occurring in a pre-term (free and bound). This is the support of the
raw pre-term. -/
def names : LamTerm α → Finset α
  | var a      => {a}
  | app t s    => t.names ∪ s.names
  | lam ⟨a, t⟩ => {a} ∪ t.names

@[simp] theorem names_var (a : α) : ⌜a⌝.names = {a} := rfl
@[simp] theorem names_app (t s : LamTerm α) : (t ◃ s).names = t.names ∪ s.names := rfl
@[simp] theorem names_lam (a : α) (t : LamTerm α) : (ƛ[a]t).names = {a} ∪ t.names := rfl

/-- Free variables of a pre-term. Characterizes the support of the alpha-equivalence
class (`Term α`), not the raw pre-term. -/
def fv : LamTerm α → Finset α
  | var a     => {a}
  | app t s   => t.fv ∪ s.fv
  | lam ⟨a, t⟩ => t.fv \ {a}

@[simp] theorem fv_var (a : α) : ⌜a⌝.fv = {a} := rfl
@[simp] theorem fv_app (t s : LamTerm α) : (t ◃ s).fv = t.fv ∪ s.fv := rfl
@[simp] theorem fv_lam (a : α) (t : LamTerm α) : (ƛ[a]t).fv = t.fv \ {a} := rfl

theorem fv_subset_names (t : LamTerm α) : t.fv ⊆ t.names := by
  induction t using names.induct with
  | case1 a => simp
  | case2 t s iht ihs => exact Finset.union_subset_union iht ihs
  | case3 a t iht =>
    intro x hx
    simp only [fv_lam, Finset.mem_sdiff, Finset.mem_singleton, names_lam, Finset.singleton_union, Finset.mem_insert] at hx ⊢
    exact Or.inr (iht hx.1)

@[simp] theorem names_equivariant (π : FinitePerm α) (t : LamTerm α) : (π • t).names = π • t.names := by
  induction t using names.induct with
  | case1 a => simp [PermType.finset_smul, Finset.image_singleton]
  | case2 t s iht ihs => simp [iht, ihs, Finset.image_union]
  | case3 a t iht => simp [iht]

@[simp] theorem fv_equivariant (π : FinitePerm α) (t : LamTerm α) : (π • t).fv = π • t.fv := by
  induction t using names.induct with
  | case1 a => simp [PermType.finset_smul, Finset.image_singleton]
  | case2 t s iht ihs => simp [iht, ihs, Finset.image_union]
  | case3 a t iht =>
    simp only [smul_lam, fv_lam, iht, PermType.finset_smul]
    have hinj : Function.Injective (⇑π : α → α) := fun _ _ h ↦ PermType.smul_injective π h
    rw [Finset.image_sdiff _ _ hinj]
    rfl

/-!
## `LamTerm` is a nominal set

The set `names t` supports the raw term `t`: any swap of two atoms outside
`names t` fixes `t`. Since `names t` is finite, every raw term is finitely
supported, giving the `Nominal` instance.

We then compute `supp` explicitly: `supp t = names t` for raw terms.
-/

theorem names_supports (t : LamTerm α) : supports t.names t := by
  rw [supports_iff_swap]
  intro a₁ a₂ ha₁ ha₂
  induction t using names.induct with
  | case1 a =>
    simp only [names_var, Finset.mem_singleton] at ha₁ ha₂
    simp [swap_apply_of_ne (Ne.symm ha₁) (Ne.symm ha₂)]
  | case2 t s iht ihs =>
    simp only [names_app, Finset.mem_union, not_or] at ha₁ ha₂
    simp [iht ha₁.1 ha₂.1, ihs ha₁.2 ha₂.2]
  | case3 a t iht =>
    simp only [names_lam, Finset.mem_union, Finset.mem_singleton, not_or] at ha₁ ha₂
    simp [swap_apply_of_ne (Ne.symm ha₁.1) (Ne.symm ha₂.1), iht ha₁.2 ha₂.2]

instance instNominal : Nominal α (LamTerm α) where
  __ := instPermType
  finSupp t := ⟨t.names, names_supports t⟩

/-! Support of each constructor. The binder is *visible* in the raw term's support:
`supp (ƛ[a] t) = {a} ∪ supp t`. This changes after quotienting (§7). -/

@[simp] theorem supp_var (a : α) : supp ⌜a⌝ = {a} := by
  apply Finset.Subset.antisymm
  · exact supp_le (names_supports ⌜a⌝)
  · intro b hb
    simp only [Finset.mem_singleton] at hb
    rw [mem_supp]
    intro s hs
    by_contra habs
    pick_new c (s ∪ {b})
    simp only [Finset.mem_union, Finset.mem_singleton, not_or] at cNew
    have hsw := (supports_iff_swap.mp hs) b c habs cNew.1
    simp only [hb, smul_var, swap_apply_left] at hsw
    exact cNew.2 ((LamTerm.var.inj hsw) ▸ hb.symm)

@[simp] theorem supp_app (t s : LamTerm α) : supp (t ◃ s) = supp t ∪ supp s := by
  apply Finset.Subset.antisymm
  · apply supp_le
    rw [supports_iff_swap]
    intro a₁ a₂ ha₁ ha₂
    simp only [Finset.mem_union] at ha₁ ha₂
    push Not at ha₁ ha₂
    simp [swap_smul_eq_of_support ha₁.1 ha₂.1, swap_smul_eq_of_support ha₁.2 ha₂.2]
  · intro a ha
    simp only [Finset.mem_union] at ha
    rw [mem_supp]
    intro u hu
    rcases ha with ht | hs
    · exact mem_supp.mp ht u (fun π hπ ↦ by
        have := hu π hπ; simp only [smul_app, app.injEq] at this; exact this.1)
    · exact mem_supp.mp hs u (fun π hπ ↦ by
        have := hu π hπ; simp only [smul_app, app.injEq] at this; exact this.2)

@[simp] theorem supp_lam (a : α) (t : LamTerm α) : supp ƛ[a]t = {a} ∪ supp t := by
  apply Finset.Subset.antisymm
  · apply supp_le
    rw [supports_iff_swap]
    intro a₁ a₂ ha₁ ha₂
    simp only [Finset.mem_union, Finset.mem_singleton, not_or] at ha₁ ha₂
    simp [swap_apply_of_ne (Ne.symm ha₁.1) (Ne.symm ha₂.1), swap_smul_eq_of_support ha₁.2 ha₂.2]
  · intro b hb
    simp only [Finset.mem_union, Finset.mem_singleton] at hb
    rw [mem_supp]
    intro u hu
    rcases hb with hba | ht
    · -- b = a (the binder)
      by_contra hna
      pick_new c (u ∪ {b} ∪ supp t)
      simp only [Finset.mem_union, Finset.mem_singleton, not_or] at cNew
      have hsw := (supports_iff_swap.mp hu) b c hna cNew.1.1
      simp only [hba, smul_lam, swap_apply_left] at hsw
      have hinj := congr_arg Bind.binder (LamTerm.lam.inj hsw)
      simp only at hinj
      exact cNew.1.2 (hinj ▸ hba.symm)
    · exact mem_supp.mp ht u (fun π hπ ↦ by
        have hsw := hu π hπ
        simp only [smul_lam] at hsw
        have := LamTerm.lam.inj hsw
        exact congr_arg Bind.body this)

/-- The support of a raw term equals its set of names (all atoms, free and bound). -/
theorem supp_eq_names (t : LamTerm α) : supp t = t.names := by
  induction t using names.induct with
  | case1 a => simp
  | case2 t s iht ihs => simp [iht, ihs]
  | case3 a t iht => simp [iht]

theorem fv_subset_supp (t : LamTerm α) : t.fv ⊆ supp t := by
  rw [supp_eq_names]; exact fv_subset_names t

end LamTerm

/-!
## Alpha-equivalence

Two raw terms are *alpha-equivalent* (`t ≈α s`) when they differ only in the
choice of bound variable names. The definition is inductive with three rules:

- **var**: `⌜a⌝ ≈α ⌜a⌝`.
- **app**: congruence — `t₁ ≈α t₂ ∧ s₁ ≈α s₂ → t₁ s₁ ≈α t₂ s₂`.
- **lam**: cofinite quantification — `ƛ[a₁] t₁ ≈α ƛ[a₂] t₂` when there exists a
  finite set `L` such that for all `c ∉ L`, swapping the binder with `c` in each
  body gives alpha-equivalent results: `swap a₁ c • t₁ ≈α swap a₂ c • t₂`.

The cofinite formulation in the lam case is equivalent to the `И`-quantifier
(`AEq.lam_iff`). It avoids choosing a single witness, making proofs (especially
transitivity) more robust.

We prove that `AEq` is an equivariant equivalence relation:
- **Equivariant**: `t ≈α s → π • t ≈α π • s` for all permutations `π`.
- **Reflexive**, **symmetric**, **transitive**.
- **Preserves free variables**: `t ≈α s → fv t = fv s`.
-/

/-- Alpha-equivalence on raw lambda terms, using cofinite quantification in the
`lam` case. -/
inductive AEq : LamTerm α → LamTerm α → Prop where
  | var (a : α) : AEq ⌜a⌝ ⌜a⌝
  | app {t₁ t₂ s₁ s₂ : LamTerm α} : AEq t₁ t₂ → AEq s₁ s₂ → AEq (t₁ ◃ s₁) (t₂ ◃ s₂)
  | lam {a₁ a₂ : α} {t₁ t₂ : LamTerm α} (L : Finset α) :
      (∀ c, c # L → AEq (swap a₁ c • t₁) (swap a₂ c • t₂)) → AEq ƛ[a₁]t₁ ƛ[a₂]t₂

/-- Notation: `t ≈α s` for `AEq t s`. -/
scoped infix:50 " ≈α " => AEq

/-! ### Inversion lemmas -/

@[simp] theorem AEq.var_iff {a b : α} : ⌜a⌝ ≈α ⌜b⌝ ↔ a = b := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .var a

theorem AEq.app_iff {t₁ t₂ s₁ s₂ : LamTerm α} : (t₁ ◃ s₁) ≈α (t₂ ◃ s₂) ↔ t₁ ≈α t₂ ∧ s₁ ≈α s₂ := by
  constructor
  · intro h; cases h; exact ⟨‹_›, ‹_›⟩
  · exact fun ⟨h₁, h₂⟩ ↦ .app h₁ h₂

/-- The lam case of `AEq` is equivalent to `И`-quantification: `ƛ[a₁] t₁ ≈α ƛ[a₂] t₂`
iff for *cofinitely many* atoms `c`, swapping the binder with `c` gives alpha-equivalent
bodies. -/
theorem AEq.lam_iff {a₁ a₂ : α} {t₁ t₂ : LamTerm α} : ƛ[a₁]t₁ ≈α ƛ[a₂]t₂ ↔ (И c, (swap a₁ c • t₁) ≈α (swap a₂ c • t₂)) := by
  constructor
  · intro h
    match h with
    | .lam L hL =>
      rw [freshQuantifier_iff]
      exact L.finite_toSet.subset fun c hc ↦ by
        simp only [Set.mem_ofPred] at hc
        rw [Finset.mem_coe]
        exact by_contra fun hcL ↦ hc (hL c (fresh_atom_finset.mpr hcL))
  · intro h
    rw [freshQuantifier_iff] at h
    exact .lam h.toFinset fun c hc ↦ by
      simp only [fresh_atom_finset, Set.Finite.mem_toFinset, Set.mem_ofPred, not_not] at hc
      exact hc

/-! ### Equivariance of alpha-equivalence

Permutations preserve alpha-equivalence. The key step in the lam case: given
`∀ c ∉ L, swap a₁ c • t₁ ≈α swap a₂ c • t₂`, we need to show the same for the
permuted terms with exception set `π • L`. For a fresh `c`, we "unpermute" it to
`π⁻¹ • c` and use the identity `swap (π • a) c • (π • t) = π • swap a (π⁻¹ • c) • t`
(i.e. `swap_smul_equivariant`). -/

theorem AEq.equivariant (π : FinitePerm α) {t s : LamTerm α} (h : t ≈α s) : (π • t) ≈α (π • s) := by
  induction h with
  | var a => exact .var (π • a)
  | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂
  | @lam a₁ a₂ t₁ t₂ L _ ih =>
    refine .lam (π • L) (fun c hc ↦ ?_)
    have hc' : (π⁻¹ • c) # L := by rwa [← fresh_equivariant_iff (π := π), smul_inv_smul]
    change AEq (swap (π • a₁) c • (π • t₁)) (swap (π • a₂) c • (π • t₂))
    rw [show swap (π • a₁) c = swap (π • a₁) (π • (π⁻¹ • c)) from by rw [smul_inv_smul],
        show swap (π • a₂) c = swap (π • a₂) (π • (π⁻¹ • c)) from by rw [smul_inv_smul],
        swap_smul_equivariant, swap_smul_equivariant]
    exact ih (π⁻¹ • c) hc'

theorem AEq.equivariant_iff (π : FinitePerm α) {t s : LamTerm α} : (π • t) ≈α (π • s) ↔ t ≈α s := by
  constructor
  · intro h
    have := AEq.equivariant π⁻¹ h
    simp only [inv_smul_smul] at this
    exact this
  · exact AEq.equivariant π

/-! ### Equivalence relation -/

theorem AEq.refl (t : LamTerm α) : t ≈α t := by
  induction t using LamTerm.names.induct with
  | case1 a => exact .var a                                      -- var
  | case2 _ _ iht ihs => exact .app iht ihs                      -- app
  | case3 a t iht =>                                             -- lam
    exact .lam {a} (fun c hc ↦ AEq.equivariant (swap a c) iht)

theorem AEq.symm {t s : LamTerm α} (h : t ≈α s) : s ≈α t := by
  induction h with
  | var a => exact .var a
  | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂
  | lam L _ ih => exact .lam L (fun c hc ↦ ih c hc)

theorem AEq.trans {t₁ t₂ t₃ : LamTerm α} (h₁₂ : t₁ ≈α t₂) (h₂₃ : t₂ ≈α t₃) : t₁ ≈α t₃ := by
  induction h₁₂ generalizing t₃ with
  | var a => exact h₂₃
  | app h₁₂t h₁₂s iht ihs =>
    match h₂₃ with
    | .app h₂₃t h₂₃s => exact .app (iht h₂₃t) (ihs h₂₃s)
  | @lam a₁ a₂ s₁ s₂ L₁₂ _ ih₁₂ =>
    match h₂₃ with
    | .lam L₂₃ hL₂₃ =>
      exact .lam (L₁₂ ∪ L₂₃) (fun c hc ↦ by
        simp only [fresh_atom_finset, Finset.mem_union, not_or] at hc
        exact ih₁₂ c (fresh_atom_finset.mpr hc.1) (hL₂₃ c (fresh_atom_finset.mpr hc.2)))

/-! ### Free variables are preserved by alpha-equivalence

This is crucial for lifting `fv` to the quotient. The proof for the lam case uses
a freshness argument: pick `c` fresh for both binders and both bodies, then the
equivariance of `fv` gives `swap a₁ c • fv(s₁) = swap a₂ c • fv(s₂)`, from which
we extract `fv(s₁) \ {a₁} = fv(s₂) \ {a₂}` by showing that `c` is not free in
either body. -/

private theorem fv_sdiff_subset_of_smul_eq {a₁ a₂ c : α} {s₁ s₂ : LamTerm α}
    (ih : swap a₁ c • s₁.fv = swap a₂ c • s₂.fv) (hc₁ : c ∉ s₁.fv) (hc₂ : c ∉ s₂.fv)
    {b : α} (hb : b ∈ s₁.fv) (hba₁ : b ≠ a₁) : b ∈ s₂.fv ∧ b ≠ a₂ := by
  have hbc : b ≠ c := fun h ↦ hc₁ (h ▸ hb)
  have hb_img : b ∈ swap a₁ c • s₁.fv := by
    rw [PermType.mem_smul_finset_iff, swap_inv, swap_apply_of_ne hba₁ hbc]; exact hb
  rw [ih, PermType.mem_smul_finset_iff, swap_inv] at hb_img
  have hba₂ : b ≠ a₂ := by
    intro heq; rw [heq, swap_apply_left] at hb_img; exact hc₂ hb_img
  rw [swap_apply_of_ne hba₂ hbc] at hb_img
  exact ⟨hb_img, hba₂⟩

/-- Alpha-equivalent raw terms have the same free variables. -/
theorem AEq.fv_eq {t₁ t₂ : LamTerm α} (h : t₁ ≈α t₂) : t₁.fv = t₂.fv := by
  induction h with
  | var a => rfl
  | app _ _ ih₁ ih₂ => simp only [LamTerm.fv_app, ih₁, ih₂]
  | @lam a₁ a₂ s₁ s₂ L _ ih =>
    choose_fresh c from L a₁ s₁ a₂ s₂
    have hc_fv₁ : c ∉ s₁.fv := fun hmem ↦ (fresh_atom_left c s₁).mp cFresh3 (LamTerm.fv_subset_supp s₁ hmem)
    have hc_fv₂ : c ∉ s₂.fv := fun hmem ↦ (fresh_atom_left c s₂).mp cFresh5 (LamTerm.fv_subset_supp s₂ hmem)
    have ih := ih c cFresh1
    rw [LamTerm.fv_equivariant, LamTerm.fv_equivariant] at ih
    simp only [LamTerm.fv_lam]
    ext b; simp only [Finset.mem_sdiff, Finset.mem_singleton]
    exact ⟨fun ⟨hb, hba₁⟩ ↦ fv_sdiff_subset_of_smul_eq ih hc_fv₁ hc_fv₂ hb hba₁,
           fun ⟨hb, hba₂⟩ ↦ fv_sdiff_subset_of_smul_eq ih.symm hc_fv₂ hc_fv₁ hb hba₂⟩

/-!
## The setoid and quotient

We package `AEq` as a `Setoid` and mark it equivariant. The quotient
`Term α := LamTerm α / AEq` is the type of lambda terms up to alpha-equivalence.
-/

instance alphaSetoid : Setoid (LamTerm α) where
  r := AEq
  iseqv := ⟨AEq.refl, fun h ↦ h.symm, fun h₁ h₂ ↦ h₁.trans h₂⟩

instance : IsEquivariantSetoid α (LamTerm α) alphaSetoid where
  equivariant_rel π {_ _} h := AEq.equivariant π h

/-- Alpha-equivalence classes of lambda terms. -/
def Term (α : Type u) [Name α] : Type u := Quotient (@alphaSetoid α _)

/-- `AEq` is a congruence for `LamTerm.lam` at the same binder. -/
private theorem aeq_lam_congr (a : α) {t₁ t₂ : LamTerm α} (h : t₁ ≈α t₂) : (ƛ[a] t₁) ≈α (ƛ[a] t₂) :=
  .lam ∅ (fun c _ ↦ AEq.equivariant (swap a c) h)

/-!
## `Term α` as a nominal set

We define the permutation action on `Term` manually (not via `instPermTypeQuotient`)
and lift the three constructors. The `Nominal` instance uses `fv` as the supporting
set; the key result is `supp t = fv t` — the least support of a quotient term is
exactly its set of free variables.

This is the payoff of the quotient construction: while raw terms have
`supp (ƛ[a] t) = {a} ∪ supp t` (binder visible), quotient terms satisfy
`supp (lam a t) = supp t \ {a}` (binder abstracted away).
-/

/-! ### Permutation action -/

instance instSMulTerm : SMul (FinitePerm α) (Term α) where
  smul π := Quotient.map (π • ·) (fun _ _ h ↦ AEq.equivariant π h)

@[simp] theorem term_smul_mk (π : FinitePerm α) (t : LamTerm α) : π • (⟦t⟧ : Term α) = ⟦π • t⟧ := rfl

instance instPermTypeTerm : PermType α (Term α) where
  one_smul t := by
    induction t using Quotient.ind with | _ t => change ⟦1 • t⟧ = ⟦t⟧; rw [one_smul]
  mul_smul π σ t := by
    induction t using Quotient.ind with | _ t => change ⟦(π * σ) • t⟧ = ⟦π • σ • t⟧; rw [mul_smul]

/-! ### Lifted constructors -/

namespace Term

def var (a : α) : Term α := ⟦LamTerm.var a⟧

def app : Term α → Term α → Term α := Quotient.map₂ LamTerm.app (fun _ _ h₁ _ _ h₂ ↦ AEq.app h₁ h₂)

def lam (a : α) : Term α → Term α := Quotient.map (fun t ↦ LamTerm.lam ⟨a, t⟩) (fun _ _ h ↦ aeq_lam_congr a h)

@[simp] theorem var_mk (a : α) : ⟦⌜a⌝⟧ = Term.var a := rfl
@[simp] theorem app_mk (t s : LamTerm α) : ⟦t ◃ s⟧ = Term.app ⟦t⟧ ⟦s⟧ := rfl
@[simp] theorem lam_mk (a : α) (t : LamTerm α) : ⟦ƛ[a]t⟧ = Term.lam a ⟦t⟧ := rfl

@[simp, nfun_simp] theorem smul_var (π : FinitePerm α) (a : α) :
    π • Term.var a = Term.var (π • a) := rfl

@[simp, nfun_simp] theorem smul_app (π : FinitePerm α) (t s : Term α) :
    π • Term.app t s = Term.app (π • t) (π • s) := by
  induction t, s using Quotient.ind₂ with | _ t s => rfl

@[simp, nfun_simp] theorem smul_lam (π : FinitePerm α) (a : α) (t : Term α) :
    π • Term.lam a t = Term.lam (π • a) (π • t) := by
  induction t using Quotient.ind with | _ t => rfl

/-! ### Constructor injectivity and disjointness

These results concern equality in `Term`, so clients never need to inspect raw
alpha-equivalence witnesses. Lambda injectivity, which uses `NameAbs`, appears
with the abstraction interface below.
-/

@[simp] theorem var_inj {a b : α} : Term.var a = Term.var b ↔ a = b := by
  constructor
  · intro h
    exact AEq.var_iff.mp (Quotient.exact h)
  · rintro rfl
    rfl

@[simp] theorem app_inj {t₁ t₂ s₁ s₂ : Term α} :
    Term.app t₁ t₂ = Term.app s₁ s₂ ↔ t₁ = s₁ ∧ t₂ = s₂ := by
  induction t₁, t₂ using Quotient.ind₂ with | _ r₁ r₂ =>
  induction s₁, s₂ using Quotient.ind₂ with | _ u₁ u₂ =>
  constructor
  · intro h
    have ⟨h₁, h₂⟩ := AEq.app_iff.mp (Quotient.exact h)
    exact ⟨Quotient.sound h₁, Quotient.sound h₂⟩
  · rintro ⟨h₁, h₂⟩
    exact congrArg₂ Term.app h₁ h₂

@[simp] theorem var_ne_app (a : α) (t₁ t₂ : Term α) : Term.var a ≠ Term.app t₁ t₂ := by
  induction t₁, t₂ using Quotient.ind₂ with | _ s₁ s₂ =>
    intro h; have := Quotient.exact h; cases this

@[simp] theorem var_ne_lam (a : α) (b : α) (t : Term α) : Term.var a ≠ Term.lam b t := by
  induction t using Quotient.ind with | _ s =>
    intro h; have := Quotient.exact h; cases this

@[simp] theorem app_ne_lam (t₁ t₂ : Term α) (a : α) (s : Term α) :
    Term.app t₁ t₂ ≠ Term.lam a s := by
  induction t₁, t₂ using Quotient.ind₂ with | _ r₁ r₂ =>
    induction s using Quotient.ind with | _ r =>
      intro h; have := Quotient.exact h; cases this

@[simp] theorem app_ne_var (t₁ t₂ : Term α) (a : α) : Term.app t₁ t₂ ≠ Term.var a :=
  (var_ne_app a t₁ t₂).symm

@[simp] theorem lam_ne_var (b : α) (t : Term α) (a : α) : Term.lam b t ≠ Term.var a :=
  (var_ne_lam a b t).symm

@[simp] theorem lam_ne_app (a : α) (s t₁ t₂ : Term α) :
    Term.lam a s ≠ Term.app t₁ t₂ :=
  (app_ne_lam t₁ t₂ a s).symm

/-! ### Free variables on the quotient

Since `AEq.fv_eq` shows alpha-equivalent terms have the same free variables, `fv` lifts cleanly to `Term α`. -/

def fv : Term α → Finset α :=
  Quotient.lift LamTerm.fv (fun _ _ h ↦ AEq.fv_eq h)

@[simp] theorem fv_mk (t : LamTerm α) : fv (⟦t⟧ : Term α) = t.fv := rfl
@[simp] theorem fv_var (a : α) : (Term.var a).fv = {a} := rfl
@[simp] theorem fv_app (t s : Term α) : (Term.app t s).fv = t.fv ∪ s.fv := by induction t, s using Quotient.ind₂ with | _ t s => rfl
@[simp] theorem fv_lam (a : α) (t : Term α) : (Term.lam a t).fv = t.fv \ {a} := by induction t using Quotient.ind with | _ t => rfl

@[simp] theorem fv_equivariant (π : FinitePerm α) (t : Term α) : (π • t).fv = π • t.fv := by
  induction t using Quotient.ind with | _ t => exact LamTerm.fv_equivariant π t

/-! ### `fv` supports `Term`

Swapping two atoms *outside* the free variables of a term yields an alpha-equivalent
raw term (`swap_fv_aeq`), hence the same quotient element. This means `fv t`
supports `t`. -/

private theorem term_eq_iff {t₁ t₂ : LamTerm α} : (⟦t₁⟧ : Term α) = ⟦t₂⟧ ↔ t₁ ≈α t₂ :=
  ⟨fun h ↦ Quotient.exact h, fun h ↦ Quotient.sound h⟩

private theorem swap_image_not_mem_fv {a c b : α} {t : LamTerm α}
    (hcfv : c ∉ t.fv) (hbc : b ≠ c) (hb : b ∈ t.fv → b = a) : swap a c • b ∉ t.fv := by
  by_cases hba : b = a
  · simp [hba, hcfv]
  · rw [swap_apply_of_ne hba hbc]; exact fun h ↦ hba (hb h)

/-- Swapping two atoms outside the free variables yields an alpha-equivalent term.
This is the key lemma connecting `fv` to the support of the quotient. -/
private theorem swap_fv_aeq (t : LamTerm α) {a₁ a₂ : α} (h₁ : a₁ ∉ t.fv) (h₂ : a₂ ∉ t.fv) : (swap a₁ a₂ • t) ≈α t := by
  cases t with
  | var a =>
    simp only [LamTerm.fv_var, Finset.mem_singleton] at h₁ h₂
    simp [swap_apply_of_ne (Ne.symm h₁) (Ne.symm h₂)]
  | app t s =>
    simp only [LamTerm.fv_app, Finset.mem_union, not_or] at h₁ h₂
    exact .app (swap_fv_aeq t h₁.1 h₂.1) (swap_fv_aeq s h₁.2 h₂.2)
  | lam r =>
    obtain ⟨a, t⟩ := r
    simp only [LamTerm.fv_lam, Finset.mem_sdiff, Finset.mem_singleton, not_and,
      not_not] at h₁ h₂
    refine .lam (t.fv ∪ {a, a₁, a₂}) (fun c hc ↦ ?_)
    simp only [fresh_atom_finset, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, not_or] at hc
    obtain ⟨hcfv, hca, hca₁, hca₂⟩ := hc
    have hfix : swap a₁ a₂ • c = c :=
      swap_apply_of_ne (fun h ↦ hca₁ h) (fun h ↦ hca₂ h)
    change AEq (swap (swap a₁ a₂ • a) c • (swap a₁ a₂ • t)) (swap a c • t)
    conv_lhs => rw [show (c : α) = swap a₁ a₂ • c from hfix.symm, swap_smul_equivariant]
    rw [← mul_smul, mul_swap_conj (swap a c) a₁ a₂, mul_smul]
    exact AEq.equivariant _ (swap_fv_aeq t
      (swap_image_not_mem_fv hcfv (fun h ↦ hca₁ h.symm) h₁)
      (swap_image_not_mem_fv hcfv (fun h ↦ hca₂ h.symm) h₂))

/-- The free variables of a term support it. -/
theorem fv_supports (t : Term α) : supports t.fv t := by
  induction t using Quotient.ind with
  | _ t =>
    erw [supports_iff_swap]
    intro a₁ a₂ ha₁ ha₂
    simp only [fv_mk] at ha₁ ha₂
    change swap a₁ a₂ • (⟦t⟧ : Term α) = ⟦t⟧
    rw [term_smul_mk, term_eq_iff]
    exact swap_fv_aeq t ha₁ ha₂

/-! ### `Nominal` instance -/

instance instNominalTerm : Nominal α (Term α) where
  __ := instPermTypeTerm
  finSupp t := ⟨t.fv, fv_supports t⟩

/-! ### Support decomposition helpers

These private lemmas extract support information from a support set for a compound
term. They are used in the proof that `supp t = fv t`. -/

private theorem supports_term_app_left {s : Finset α} {t₁ t₂ : LamTerm α}
    (hs : supports s (⟦LamTerm.app t₁ t₂⟧ : Term α)) : supports s (⟦t₁⟧ : Term α) :=
  fun π hπ ↦ by
    have h := hs π hπ
    change ⟦π • LamTerm.app t₁ t₂⟧ = ⟦LamTerm.app t₁ t₂⟧ at h
    rw [LamTerm.smul_app, term_eq_iff, AEq.app_iff] at h
    change ⟦π • t₁⟧ = ⟦t₁⟧; rw [term_eq_iff]; exact h.1

private theorem supports_term_app_right {s : Finset α} {t₁ t₂ : LamTerm α}
    (hs : supports s (⟦LamTerm.app t₁ t₂⟧ : Term α)) : supports s (⟦t₂⟧ : Term α) :=
  fun π hπ ↦ by
    have h := hs π hπ
    change ⟦π • LamTerm.app t₁ t₂⟧ = ⟦LamTerm.app t₁ t₂⟧ at h
    rw [LamTerm.smul_app, term_eq_iff, AEq.app_iff] at h
    change ⟦π • t₂⟧ = ⟦t₂⟧; rw [term_eq_iff]; exact h.2

private theorem supports_term_lam_body {s : Finset α} {a : α} {t : LamTerm α}
    (hs : supports s (⟦LamTerm.lam ⟨a, t⟩⟧ : Term α)) : supports (s ∪ {a}) (⟦t⟧ : Term α) := by
  rw [supports_iff_swap]
  intro c₁ c₂ hc₁ hc₂
  simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hc₁ hc₂
  have hsw := (supports_iff_swap.mp hs) c₁ c₂ hc₁.1 hc₂.1
  change ⟦swap c₁ c₂ • LamTerm.lam ⟨a, t⟩⟧ = ⟦LamTerm.lam ⟨a, t⟩⟧ at hsw
  rw [LamTerm.smul_lam, swap_apply_of_ne (Ne.symm hc₁.2) (Ne.symm hc₂.2),
      term_eq_iff] at hsw
  match hsw with
  | .lam L hL =>
    pick_new d (L ∪ {a})
    simp only [Finset.mem_union, Finset.mem_singleton, not_or] at dNew
    have := hL d (fresh_atom_finset.mpr dNew.1)
    change swap c₁ c₂ • (⟦t⟧ : Term α) = ⟦t⟧
    rw [term_smul_mk, term_eq_iff]
    exact AEq.equivariant_iff (swap a d) |>.mp this

/-! ### `supp = fv`

The central result of this section: the least support of a quotient term is
exactly its free variables. The upper bound (`supp t ⊆ fv t`) follows from
`fv_supports`. The lower bound (`fv t ⊆ supp t`) is proved by showing that
every free variable belongs to every supporting set — by induction on the raw
term, using the support decomposition helpers above. -/

@[simp] theorem supp_eq_fv (t : Term α) : supp t = t.fv := by
  apply le_antisymm
  · exact supp_le (fv_supports t)
  · induction t using Quotient.ind with
    | _ t =>
      intro b hb
      simp only [fv_mk] at hb
      erw [mem_supp]; intro s hs
      exact supp_eq_fv_aux t hb s hs
  where
    supp_eq_fv_aux (t : LamTerm α) {b : α} (hb : b ∈ t.fv) (s : Finset α)
        (hs : supports s (⟦t⟧ : Term α)) : b ∈ s := by
      cases t with
      | var a =>
        simp only [LamTerm.fv_var, Finset.mem_singleton] at hb; subst hb
        by_contra hbs
        pick_new c (s ∪ {b})
        simp only [Finset.mem_union, Finset.mem_singleton, not_or] at cNew
        have hsw := (supports_iff_swap.mp hs) b c hbs cNew.1
        change ⟦swap b c • LamTerm.var b⟧ = ⟦LamTerm.var b⟧ at hsw
        rw [LamTerm.smul_var, swap_apply_left, term_eq_iff, AEq.var_iff] at hsw
        exact cNew.2 hsw
      | app t₁ t₂ =>
        simp only [LamTerm.fv_app, Finset.mem_union] at hb
        rcases hb with hb₁ | hb₂
        · exact supp_eq_fv_aux t₁ hb₁ s (supports_term_app_left hs)
        · exact supp_eq_fv_aux t₂ hb₂ s (supports_term_app_right hs)
      | lam r =>
        obtain ⟨a, t⟩ := r
        simp only [LamTerm.fv_lam, Finset.mem_sdiff, Finset.mem_singleton] at hb
        have hb_sa := supp_eq_fv_aux t hb.1 (s ∪ {a}) (supports_term_lam_body hs)
        simp only [Finset.mem_union, Finset.mem_singleton] at hb_sa
        exact hb_sa.elim id (fun h ↦ absurd h hb.2)

/-! Convenient corollaries of `supp_eq_fv`: -/

@[simp] theorem supp_term_var (a : α) : supp (Term.var a) = {a} := by simp
@[simp] theorem supp_term_app (t s : Term α) : supp (Term.app t s) = supp t ∪ supp s := by simp
@[simp] theorem supp_term_lam (a : α) (t : Term α) : supp (Term.lam a t) = supp t \ {a} := by simp

/-! ### Freshness lemmas -/

@[simp] theorem fresh_term_var (x : α) (a : α) : x # Term.var a ↔ x ≠ a := by
  simp

@[simp] theorem fresh_term_app (x : α) (t₁ t₂ : Term α) :
    x # Term.app t₁ t₂ ↔ x # t₁ ∧ x # t₂ := by
  simp [Finset.mem_union, not_or]

theorem fresh_term_lam (x : α) (a : α) (t : Term α) :
    x # Term.lam a t ↔ (x = a ∨ x # t) := by
  simp only [fresh_atom_left, supp_term_lam, Finset.mem_sdiff, Finset.mem_singleton,
    not_and_or, not_not]
  exact or_comm

theorem fresh_term_lam_of_fresh (x : α) (a : α) (t : Term α) (h : x # t) :
    x # Term.lam a t := by
  rw [fresh_term_lam]; exact Or.inr h

theorem fresh_term_lam_of_eq (a : α) (t : Term α) : a # Term.lam a t := by
  rw [fresh_term_lam]; exact Or.inl rfl

/-!
## Bridge to `NameAbs`

The lemma `term_lam_eq_iff` connects equality of `Term.lam` to equality of
`NameAbs`: two lambda terms `lam a₁ t₁` and `lam a₂ t₂` are equal on the quotient
if and only if `⟪a₁⟫ t₁ = ⟪a₂⟫ t₂` as name abstractions. This bridges `Term.lam`
to the full `NameAbs` API (`abs_eq_iff`, `abs_eq_swap`, `fresh_abs`, etc.).
-/

open MulAction PermType in
/-- Bridge from `RawAbs` to `NameAbs`: `⟨a, t⟩ ↦ ⟪a⟫t`. -/
def RawAbs.toNameAbs {X : Type u} [Nominal α X] (r : Bind α X) : NameAbs α X :=
  ⟪r.binder⟫ r.body

/-- Two lambda terms on the quotient are equal iff their binder-body pairs form the
same name abstraction. -/
theorem term_lam_eq_iff {a₁ a₂ : α} {t₁ t₂ : Term α} :
    Term.lam a₁ t₁ = Term.lam a₂ t₂ ↔ ⟪a₁⟫t₁ = ⟪a₂⟫t₂ := by
  induction t₁, t₂ using Quotient.ind₂ with
  | _ s₁ s₂ =>
    erw [← lam_mk, ← lam_mk, NameAbs.abs_eq_iff_freshQuantifier]
    constructor
    · -- (→) AEq cofinite → И on Term quotient
      intro h
      exact (AEq.lam_iff.mp (Quotient.exact h)).mono fun c hc ↦ Quotient.sound hc
    · -- (←) И on Term quotient → AEq cofinite
      intro h
      exact Quotient.sound (AEq.lam_iff.mpr (h.mono fun c hc ↦ Quotient.exact hc))

/-! ### Fresh-binder inversion and alignment

Freshness here concerns the lambda term, hence its free variables. In particular,
a chosen atom may equal the current binder; it need not be fresh for the body.
No distinct-binder or freshness-of-bound-names assumptions are required.
-/

/-- At a fixed binder, equality of lambda terms is equality of their bodies. -/
@[simp] theorem lam_inj {a : α} {t s : Term α} :
    Term.lam a t = Term.lam a s ↔ t = s := by
  rw [term_lam_eq_iff, NameAbs.abs_same_name_iff]

/-- Rename a binder to any atom fresh for the lambda term. The atom can be the
original binder, even when it occurs freely in the body. -/
theorem lam_eq_swap {a b : α} {t : Term α} (hb : b # Term.lam a t) :
    Term.lam a t = Term.lam b (swap a b • t) := by
  rcases (fresh_term_lam b a t).mp hb with rfl | hb
  · simp
  · exact term_lam_eq_iff.mpr (NameAbs.abs_eq_swap hb)

/-- Invert a lambda equality at a prescribed fresh binder: the body is exactly
obtained by swapping the original binder with the chosen one. -/
theorem lam_eq_iff_at_fresh {a c : α} {t s : Term α}
    (hc : c # Term.lam a t) :
    Term.lam a t = Term.lam c s ↔ swap a c • t = s := by
  rw [lam_eq_swap hc, lam_inj]

/-- Every atom fresh for a lambda term determines a unique body representing it. -/
theorem exists_lam_eq_at_fresh {a c : α} {t : Term α}
    (hc : c # Term.lam a t) : ∃! s, Term.lam a t = Term.lam c s := by
  refine ⟨swap a c • t, lam_eq_swap hc, ?_⟩
  intro s hs
  exact ((lam_eq_iff_at_fresh hc).mp hs).symm

/-- Align two lambda terms at any atom fresh for both lambda terms. Freshness
for their bodies or original binders is not required. -/
theorem lam_eq_iff_common_fresh {a b c : α} {t s : Term α}
    (hc₁ : c # Term.lam a t) (hc₂ : c # Term.lam b s) :
    Term.lam a t = Term.lam b s ↔ swap a c • t = swap b c • s := by
  rw [lam_eq_swap hc₁, lam_eq_swap hc₂, lam_inj]

end Term

end LambdaCalculus
