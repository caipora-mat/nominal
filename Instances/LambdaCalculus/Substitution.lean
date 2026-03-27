import Instances.LambdaCalculus.Recursion

/-!
# Capture-Avoiding Substitution

With the recursion combinator in hand, we instantiate it to define capture-avoiding
substitution `t[x := s]` on `Term α` and prove its standard properties.

## The instantiation

Substitution is `recNoContext` with:

| Parameter | Value                                 | Support        |
|-----------|---------------------------------------|----------------|
| `fᵥ`      | `fun a => if a = x then s else var a` | `{x} ∪ supp s` |
| `fₐ`      | `fun (r₁, r₂) => app r₁ r₂`           | `∅`            |
| `f_L`     | `fun (a, r) => lam a r`               | `∅`            |
| `A`       | `{x} ∪ supp s`                        | —              |
|-----------|---------------------------------------|----------------|

The app and lam constructor NFuns are fully equivariant (empty support). Only `fᵥ` has
non-empty support, since it inspects `x` and returns `s`. The FCB condition holds because
`a # lam a r` (the binder is always fresh for its own abstraction).

## Theorems

We prove six standard properties:

1. **Computation rules**: `subst_var`, `subst_app`, `subst_lam` — the defining equations.
2. **Forget lemma** (`subst_fresh`): `x # t → t[x := s] = t` — Urban's Lemma 16.
3. **Freshness propagation** (`subst_fresh_of_fresh`): `a # t → a # s → a # t[x := s]`.
4. **Equivariance** (`subst_equivariant`): `π • t[x := s] = (π • t)[π • x := π • s]`.
5. **Substitution lemma** (`subst_lemma`): Barendregt's substitution lemma,
   `x ≠ y → x # L → M[x := N][y := L] = M[y := L][x := N[y := L]]`.
6. **Support bound** (`supp_subst_le`): `supp (t[x := s]) ⊆ (supp t \ {x}) ∪ supp s`.

Each proof follows the same pattern: induction on `t` via `strong_ind_finset`, with an
avoidance set covering the free names of all relevant terms. The lam case derives the
needed freshness conditions directly from `c ∉ A`.

## References

* Urban, *Nominal Techniques in Isabelle/HOL*, JAR 2008, Section 6, equation (24)
* Pitts, *Alpha-Structural Recursion and Induction*, JACM 2006, Example 4.2
-/

namespace LambdaCalculus

open Nominal.Core Nominal.Set NameAbs

universe u

variable {α : Type u} [Name α]

namespace Term

/-!
## §7. NFun constructions for substitution
-/

/-- Variable-case NFun: `fun a => if a = x then s else var a`.

The only constructor function with non-empty support (`{x} ∪ supp s`). -/
private def substFv (x : α) (s : Term α) : NFun α α (Term α) :=
  NFun.ofSupports ⟨fun a ↦ if a = x then s else Term.var a⟩ ({x} ∪ supp s) (by
    rw [supports_pfun_iff]
    intro π hπ a
    have hx : π • x = x := by rw [PermType.atoms_smul]; exact hπ (Finset.mem_union_left _ (Finset.mem_singleton_self x))
    have hs : π • s = s := supp_supports s π (fun b hb ↦ hπ (Finset.mem_union_right _ hb))
    simp only [PFun.coe_mk]
    by_cases ha : a = x
    · subst ha; simp [hx, hs]
    · have hne : π • a ≠ x := fun heq ↦ ha (PermType.smul_injective π (heq.trans hx.symm))
      rw [if_neg hne, if_neg ha, smul_var])

/-- App-case NFun: `fun (r₁, r₂) => app r₁ r₂`. Fully equivariant (empty support). -/
private def substFa : NFun α (Term α × Term α) (Term α) :=
  NFun.ofSupports ⟨fun p => Term.app p.1 p.2⟩ ∅ (by
    rw [supports_pfun_iff]
    intro π _ p
    simp [smul_app])

/-- Lam-case NFun: `fun (a, r) => lam a r`. Fully equivariant (empty support). -/
private def substFL : NFun α (α × Term α) (Term α) :=
  NFun.ofSupports ⟨fun p => Term.lam p.1 p.2⟩ ∅ (by
    rw [supports_pfun_iff]
    intro π _ p
    simp [smul_lam])

@[simp] private theorem substFv_apply (x : α) (s : Term α) (a : α) :
    substFv x s a = if a = x then s else Term.var a := rfl

@[simp] private theorem substFa_apply (p : Term α × Term α) :
    substFa p = Term.app p.1 p.2 := rfl

@[simp] private theorem substFL_apply (p : α × Term α) :
    substFL p = Term.lam p.1 p.2 := rfl

/-!
## §8. Substitution definition
-/

/-- Capture-avoiding substitution on alpha-equivalence classes.

Defined via `recNoContext` with support set `A = {x} ∪ supp s`. -/
noncomputable def subst (t : Term α) (x : α) (s : Term α) : Term α :=
  recNoContext (substFv x s) substFa substFL ({x} ∪ supp s)
    (substFv_supp_le x s) (substFa_supp_le x s) (substFL_supp_le x s) (substFL_fcb x s) t
where
  substFv_supp_le (x : α) (s : Term α) : supp (substFv x s) ⊆ {x} ∪ supp s :=
    supp_le (NFun.ofSupports_supports _ _ _)
  substFa_supp_le (x : α) (s : Term α) : supp (substFa : NFun α (Term α × Term α) (Term α)) ⊆ {x} ∪ supp s :=
    (supp_le (NFun.ofSupports_supports _ _ _)).trans (Finset.empty_subset _)
  substFL_supp_le (x : α) (s : Term α) : supp (substFL : NFun α (α × Term α) (Term α)) ⊆ {x} ∪ supp s :=
    (supp_le (NFun.ofSupports_supports _ _ _)).trans (Finset.empty_subset _)
  substFL_fcb (x : α) (s : Term α) : ∀ (a : α) (y : Term α), a # ({x} ∪ supp s : Finset α) → a # substFL (a, y) := by
    intro a y _
    simp only [substFL_apply, fresh_atom_left, supp_term_lam]
    exact Finset.notMem_sdiff_of_mem_right (Finset.mem_singleton_self a)

scoped notation:max t "[" x " := " s "]" => subst t x s

/-!
## §9. Computation lemmas
-/

@[simp] theorem subst_var (a x : α) (s : Term α) :
    (Term.var a)[x := s] = if a = x then s else Term.var a := by simp [subst]

@[simp] theorem subst_app (t₁ t₂ : Term α) (x : α) (s : Term α) :
    (Term.app t₁ t₂)[x := s] = Term.app (t₁[x := s]) (t₂[x := s]) := by simp [subst]

/-- Lambda equation: when `a # (x, s)`, substitution pushes under the binder.

This is the nominal version of Barendregt's variable convention: the bound variable `a`
is distinct from the substitution variable `x` and does not occur free in `s`. -/
theorem subst_lam (a : α) (t : Term α) (x : α) (s : Term α) (ha : a # (x, s)) : (Term.lam a t)[x := s] = Term.lam a (t[x := s]) := by
  have haA : a # ({x} ∪ supp s : Finset α) := by
    rw [fresh_atom_finset, Finset.mem_union, not_or, Finset.mem_singleton]
    exact ⟨(fresh_atoms a x).mp (fresh_prod_right.mp ha).1, (fresh_atom_left a s).mp (fresh_prod_right.mp ha).2⟩
  unfold subst
  rw [recNoContext_lam _ _ _ _ _ _ _ _ _ _ haA]
  simp

/-- Binder renaming: `b # t → (lam a t)[x := s] = (lam b (swap a b • t))[x := s]`.

A pure consequence of alpha-equivalence — does not require `b # (x, s)`. -/
theorem subst_lam_rename (a b : α) (t : Term α) (x : α) (s : Term α) (hb : b # t) :
    (Term.lam a t)[x := s] = (Term.lam b (swap a b • t))[x := s] := by
  simp only [subst]
  exact recNoContext_lam_rename _ _ _ _ _ _ _ _ a b t hb

seal subst

/-!
## §10. Substitution theorems

The four main theorems about substitution. Each is proved by `strong_ind_finset` on the
term, with an avoidance set covering the free names of all relevant terms.
-/

/-- **Forget lemma** (Urban's Lemma 16): substituting a fresh variable has no effect.

*Proof.* By `strong_ind_finset` on `t` with avoidance set `{x} ∪ supp s`. The lam case
uses `a ∉ {x} ∪ supp s` to derive `a ≠ x` and `a # s`, then `x # lam a t` gives `x # t`
(ruling out `x = a`) to apply the IH. -/
theorem subst_fresh (x : α) (t s : Term α) (h : x # t) : t[x := s] = t := by
  induction t using strong_ind_finset ({x} ∪ supp s) with
  | hVar a =>
    simp only [subst_var, fresh_term_var] at h ⊢
    exact if_neg h.symm
  | hApp t₁ t₂ ih₁ ih₂ =>
    rw [fresh_term_app] at h
    simp [ih₁ h.1, ih₂ h.2]
  | hLam a t ha ih =>
    rw [Finset.mem_union, Finset.mem_singleton, not_or] at ha
    have haxs : a # (x, s) :=
      fresh_prod_right.mpr ⟨(fresh_atoms a x).mpr ha.1, (fresh_atom_left a s).mpr ha.2⟩
    have hxt : x # t := by
      rw [fresh_term_lam] at h
      exact h.elim (fun heq ↦ absurd heq.symm ha.1) id
    rw [subst_lam a t x s haxs, ih hxt]

/-- Freshness propagation: `a # t → a # s → a # t[x := s]`. -/
theorem subst_fresh_of_fresh (a : α) (t : Term α) (x : α) (s : Term α)
    (hat : a # t) (has : a # s) : a # t[x := s] := by
  induction t using strong_ind_finset ({a, x} ∪ supp s) with
  | hVar b =>
    simp only [subst_var]
    split
    · exact has
    · exact hat
  | hApp t₁ t₂ ih₁ ih₂ =>
    rw [fresh_term_app] at hat
    simp only [subst_app, fresh_term_app]
    exact ⟨ih₁ hat.1, ih₂ hat.2⟩
  | hLam c t hc ih =>
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at hc
    obtain ⟨⟨hca, hcx⟩, hcs⟩ := hc
    have hcxs : c # (x, s) :=
      fresh_prod_right.mpr ⟨(fresh_atoms c x).mpr hcx,
        (fresh_atom_left c s).mpr hcs⟩
    rw [subst_lam c t x s hcxs]
    rw [fresh_term_lam] at hat ⊢
    exact hat.elim Or.inl (fun hfresh ↦ Or.inr (ih hfresh))

theorem subst_congr (t : Term α) (a : α) {p q : Term α} (h : p = q) : t[a := p] = t[a := q] := by subst h; rfl

/-
### Performance: `seal subst` + `seal Fresh in`

Two `seal` commands are needed to avoid deterministic timeouts in `subst_equivariant`:

1. **`seal subst`** (above): prevents the unifier from diving into
   `subst` → `recNoContext` → `Classical.choose` → `WellFounded.fix` when `rw`
   pattern-matches on the main goal. Without this, backward rewrites like
   `rw [← subst_lam ...]` trigger exponential `isDefEq` blowup.

2. **`seal Fresh in`** : prevents `rw [← hcπ]` from triggering expensive
   `whnf` on a `Fresh`-pair goal. `Fresh x y` unfolds to `Disjoint (supp x) (supp y)`,
   and rewriting `c` → `π • c` inside this forces Lean to normalize
   `supp (π • x, π • s)` through `supp_prod` and the `Nominal` instance for `Term α`
   (a quotient type), causing exponential blowup. Sealing `Fresh` keeps the goal opaque
   during the rewrite.

See also Mathlib PR #24944 and leanprover.zulipchat.com #287929 "simp timeout at whnf"
for the same pattern.
-/

seal Fresh in
/-- **Equivariance of substitution**: `π • t[x := s] = (π • t)[π • x := π • s]`.

*Proof.* By `strong_ind_finset` on `t` with avoidance set `supp π ∪ {x} ∪ supp s`. -/
theorem subst_equivariant (π : FinitePerm α) (t : Term α) (x : α) (s : Term α) :
    π • (t[x := s]) = (π • t)[π • x := π • s] := by
  induction t using strong_ind_finset (supp π ∪ {x} ∪ supp s) with
  | hVar a =>
    simp only [subst_var, smul_var]
    by_cases ha : a = x
    · subst ha; simp
    · rw [if_neg ha, if_neg (fun h ↦ ha (PermType.smul_injective π h)), smul_var]
  | hApp _ _ ih₁ ih₂ => simp only [subst_app, smul_app, ih₁, ih₂]
  | hLam c t hc ih =>
    simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hc
    obtain ⟨⟨hcπ, hcx⟩, hcs⟩ := hc
    have hcπ : π • c = c := fresh_finitePerm.mp ((fresh_atom_left c π).mpr hcπ)
    have hcxs : c # (x, s) := fresh_prod_right.mpr ⟨(fresh_atoms c x).mpr hcx, (fresh_atom_left c s).mpr hcs⟩
    have hcxs' : c # (π • x, π • s) := by rw [← hcπ]; exact fresh_equivariant π hcxs
    rw [subst_lam c t x s hcxs, smul_lam, hcπ, ih]
    rw [← subst_lam c (π • t) (π • x) (π • s) hcxs', smul_lam, hcπ]

seal Fresh in
/-- **Substitution composition** (Barendregt's substitution lemma):
`x ≠ y → x # L → M[x := N][y := L] = M[y := L][x := N[y := L]]`.

This is the main payoff of the freshness machinery. It says that two substitutions
commute (up to adjusting the replacement term) when their variables are distinct and
the first variable is fresh for the second replacement.

*Proof.* By `strong_ind_finset` on `M` with avoidance set `{x, y} ∪ supp N ∪ supp L`:
- **var a**: three sub-cases (`a = x`, `a = y`, neither), each resolved by `subst_var`.
- **app**: distribute substitution, apply IHs.
- **lam c M**: `c ∉ {x, y} ∪ supp N ∪ supp L` gives `c ≠ x`, `c ≠ y`, `c # N`, `c # L`.
  Push all four substitutions under the binder via `subst_lam`, apply the IH. The freshness
  `c # N[y := L]` follows from `subst_fresh_of_fresh`. -/
theorem subst_subst (x y : α) (M N L : Term α)
    (hxy : x ≠ y) (hxL : x # L) : M[x := N][y := L] = M[y := L][x := N[y := L]] := by
  induction M using strong_ind_finset ({x, y} ∪ supp N ∪ supp L) with
  | hVar a =>
    simp only [subst_var]
    by_cases hax : a = x
    · subst hax; simp [hxy]
    · by_cases hay : a = y
      · subst hay; simp [hax, subst_fresh x L _ hxL]
      · simp [hax, hay]
  | hApp M₁ M₂ ih₁ ih₂ =>
    simp only [subst_app, ih₁, ih₂]
  | hLam c M hc ih =>
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at hc
    obtain ⟨⟨⟨hcx, hcy⟩, hcN⟩, hcL⟩ := hc
    have hcxN : c # (x, N) := fresh_prod_right.mpr ⟨(fresh_atoms c x).mpr hcx, (fresh_atom_left c N).mpr hcN⟩
    have hcyL : c # (y, L) := fresh_prod_right.mpr ⟨(fresh_atoms c y).mpr hcy, (fresh_atom_left c L).mpr hcL⟩
    have hcNyL : c # N[y := L] := subst_fresh_of_fresh c N y L ((fresh_atom_left c N).mpr hcN) ((fresh_atom_left c L).mpr hcL)
    have hcxNyL : c # (x, N[y := L]) := fresh_prod_right.mpr ⟨(fresh_atoms c x).mpr hcx, hcNyL⟩
    rw [subst_lam c M x N hcxN, subst_lam c (M[x := N]) y L hcyL,
        subst_lam c M y L hcyL, subst_lam c (M[y := L]) x _ hcxNyL, ih]

/-!
## §11. Support bound for substitution

Substitution can only shrink (or shift) the free-variable set: substituting `x := s`
in `t` removes `x` from the support and adds the support of `s`.

*Proof.* By `strong_ind_finset` on `t` with avoidance set `{x} ∪ supp s`:
- **var a**: if `a = x` then the result is `s` and `supp s ⊆ _ ∪ supp s`; otherwise
  `{a} ⊆ {a} \ {x} ∪ supp s` since `a ≠ x`.
- **app**: distribute, union the IH bounds.
- **lam c t**: `c ∉ {x} ∪ supp s` gives `c ≠ x` and `c # s`. Push `subst` under `lam`,
  then remove `{c}` from both sides of the IH. The `sdiff_right_comm` and
  `union_sdiff_distrib` Finset lemmas handle the set arithmetic.
-/

theorem supp_subst_le (t : Term α) (x : α) (s : Term α) :
    supp (t[x := s]) ⊆ (supp t \ {x}) ∪ supp s := by
  induction t using strong_ind_finset ({x} ∪ supp s) with
  | hVar a =>
    simp only [subst_var]
    split
    · exact Finset.subset_union_right
    · next hne =>
      simp only [supp_term_var]
      exact Finset.singleton_subset_iff.mpr (Finset.mem_union_left _
        (Finset.mem_sdiff.mpr ⟨Finset.mem_singleton_self a,
          fun h ↦ hne (Finset.mem_singleton.mp h)⟩))
  | hApp t₁ t₂ ih₁ ih₂ =>
    simp only [subst_app, supp_term_app]
    exact Finset.union_subset
      (ih₁.trans (Finset.union_subset_union
        (Finset.sdiff_subset_sdiff Finset.subset_union_left (Finset.Subset.refl _))
        (Finset.Subset.refl _)))
      (ih₂.trans (Finset.union_subset_union
        (Finset.sdiff_subset_sdiff Finset.subset_union_right (Finset.Subset.refl _))
        (Finset.Subset.refl _)))
  | hLam c t hc ih =>
    rw [Finset.mem_union, Finset.mem_singleton, not_or] at hc
    have hcxs : c # (x, s) :=
      fresh_prod_right.mpr ⟨(fresh_atoms c x).mpr hc.1, (fresh_atom_left c s).mpr hc.2⟩
    rw [subst_lam c t x s hcxs]
    simp only [supp_term_lam]
    have h1 : supp (t[x := s]) \ {c} ⊆ ((supp t \ {x}) ∪ supp s) \ {c} :=
      Finset.sdiff_subset_sdiff ih (Finset.Subset.refl _)
    rw [Finset.union_sdiff_distrib, sdiff_right_comm] at h1
    exact h1.trans (Finset.union_subset_union_right (Finset.sdiff_subset))

end Term

end LambdaCalculus
