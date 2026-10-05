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

The public interface includes:

1. **Computation rules**: `subst_var`, `subst_app`, `subst_lam` — the defining equations.
2. **Forget lemma** (`subst_fresh`): `x # t → t[x := s] = t` — Urban's Lemma 16.
3. **Freshness propagation** (`subst_fresh_of_fresh`): `a # t → a # s → a # t[x := s]`.
4. **Equivariance** (`subst_equivariant`): `π • t[x := s] = (π • t)[π • x := π • s]`.
5. **Substitution lemma** (`subst_subst`): Barendregt's substitution lemma,
   `x ≠ y → x # L → M[x := N][y := L] = M[y := L][x := N[y := L]]`.
6. **Support bound** (`supp_subst_le`): `supp (t[x := s]) ⊆ (supp t \ {x}) ∪ supp s`.
7. **Binder compatibility** (`subst_rename`, `subst_eq_of_lam_eq`): the substituted
   body used in contraction is independent of the presentation of its abstraction.
   The replacement is arbitrary, including terms containing either binder freely.
8. **Identity and variable renaming** (`subst_var_self`, `subst_var_eq_swap`).

The inductive proofs use `strong_ind_finset`, with an avoidance set covering the
free names of all relevant terms. The lam case derives the needed freshness
conditions directly from `c ∉ A`; the interface corollaries reuse these results.

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
private theorem substFv_supports (x : α) (s : Term α) :
    supports ({x} ∪ supp s) (⟨fun a ↦ if a = x then s else Term.var a⟩ : PFun α α (Term α)) := by
  supports_nfun from x s

-- The least support occurs only in the proof argument, keeping the handler computable.
private def substFv (x : α) (s : Term α) : NFun α α (Term α) :=
  NFun.ofFun (fun a ↦ if a = x then s else Term.var a)
    ⟨{x} ∪ supp s, substFv_supports x s⟩

/-- App-case NFun: `fun (r₁, r₂) => app r₁ r₂`. Fully equivariant (empty support). -/
private def substFa : NFun α (Term α × Term α) (Term α) :=
  NFun.equivariant (fun p => Term.app p.1 p.2) (by intro π p; simp)

/-- Lam-case NFun: `fun (a, r) => lam a r`. Fully equivariant (empty support). -/
private def substFL : NFun α (α × Term α) (Term α) :=
  NFun.equivariant (fun p => Term.lam p.1 p.2) (by intro π p; simp)

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
    NFun.supp_ofSupports_le _ _ (substFv_supports x s)
  substFa_supp_le (x : α) (s : Term α) : supp (substFa : NFun α (Term α × Term α) (Term α)) ⊆ {x} ∪ supp s := by
    simp [substFa]
  substFL_supp_le (x : α) (s : Term α) : supp (substFL : NFun α (α × Term α) (Term α)) ⊆ {x} ∪ supp s := by
    simp [substFL]
  substFL_fcb (x : α) (s : Term α) : ∀ (a : α) (y : Term α), a # ({x} ∪ supp s : Finset α) → a # substFL (a, y) :=
    NFun.fcb_of_binder substFL fresh_term_lam_of_eq ({x} ∪ supp s)

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
  exact congrArg (fun u : Term α ↦ u[x := s])
    (term_lam_eq_iff.mpr (NameAbs.abs_eq_swap hb))

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
    exact ite_eq_right h.symm
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

Both boundaries are retained from the original development. The 4.34.1 review
reproduced a timeout after removing only `seal Fresh in`; removing only `seal subst`
still compiled. Thus that review establishes the need for the Fresh boundary in
this proof, not the independent necessity of both seals.

1. **`seal subst`** (above): prevents the unifier from diving into
   `subst` → `recNoContext` → `Classical.choose` → `WellFounded.fix` when `rw`
   pattern-matches on the main goal. This guards backward rewrites such as
   `rw [← subst_lam ...]` against unfolding the iterator implementation.

2. **`seal Fresh in`** : prevents `rw [← hcπ]` from triggering expensive
   `whnf` on a `Fresh`-pair goal. `Fresh x y` unfolds to `Disjoint (supp x) (supp y)`,
   and rewriting `c` → `π • c` inside this forces Lean to normalize
   `supp (π • x, π • s)` through `supp_prod` and the `Nominal` instance for `Term α`
   (a quotient type), causing costly normalization. Sealing `Fresh` keeps the goal opaque
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
    · rw [ite_eq_right ha, ite_eq_right (fun h ↦ ha (PermType.smul_injective π h)), smul_var]
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
## Binder compatibility for contraction

`subst_lam_rename` above rewrites substitution of an entire lambda. The results
here instead compare substitutions of its *body* at its bound atom, as needed
for beta contraction. Neither binder needs to be fresh for the replacement.
-/

/-- Substitution of a variable by itself is the identity on every quotient term. -/
@[simp] theorem subst_var_self (t : Term α) (a : α) : t[a := var a] = t := by
  induction t using strong_ind_finset {a} with
  | hVar b => by_cases h : b = a <;> simp [h]
  | hApp t u iht ihu => simp [iht, ihu]
  | hLam b t hb ih =>
    have hba : b ≠ a := by simpa using hb
    rw [subst_lam b t a (var a) (fresh_prod_right.mpr
      ⟨(fresh_atoms b a).mpr hba, (fresh_term_var b a).mpr hba⟩), ih]

private theorem subst_rename_of_fresh (a b : α) (t s : Term α) (hb : b # t) :
    t[a := s] = (swap a b • t)[b := s] := by
  induction t using strong_ind_finset ({a, b} ∪ supp s) with
  | hVar c =>
    have hcb : c ≠ b := ((fresh_term_var b c).mp hb).symm
    by_cases hca : c = a
    · subst c; simp
    · rw [smul_var, swap_apply_of_ne hca hcb]
      simp [hca, hcb]
  | hApp t u iht ihu =>
    obtain ⟨hbt, hbu⟩ := (fresh_term_app b t u).mp hb
    simp only [smul_app, subst_app, iht hbt, ihu hbu]
  | hLam c t hc ih =>
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at hc
    obtain ⟨⟨hca, hcb⟩, hcs⟩ := hc
    have hcs : c # s := (fresh_atom_left c s).mpr hcs
    have hcas : c # (a, s) := fresh_prod_right.mpr ⟨(fresh_atoms c a).mpr hca, hcs⟩
    have hcbs : c # (b, s) := fresh_prod_right.mpr ⟨(fresh_atoms c b).mpr hcb, hcs⟩
    have hbt : b # t := ((fresh_term_lam b c t).mp hb).resolve_left (Ne.symm hcb)
    rw [smul_lam, swap_apply_of_ne hca hcb,
      subst_lam c t a s hcas, subst_lam c (swap a b • t) b s hcbs, ih hbt]

/-- Renaming a binder and its body preserves the substituted body used in
contraction. The new binder `b` need only be fresh for `lam a t`, equivalently
`b = a ∨ b # t`; no freshness assumption on the replacement `s` is needed. -/
theorem subst_rename (a b : α) (t s : Term α) (hb : b # lam a t) :
    t[a := s] = (swap a b • t)[b := s] := by
  rcases (fresh_term_lam b a t).mp hb with h | h
  · subst b; simp
  · exact subst_rename_of_fresh a b t s h

/-- Substituting a variable for the bound atom agrees with swapping, provided
its atom is fresh for the abstraction. This includes the case `a = b`. -/
theorem subst_var_eq_swap (a b : α) (t : Term α) (hb : b # lam a t) :
    t[a := var b] = swap a b • t := by
  rw [subst_rename a b t (var b) hb, subst_var_self]

/-- Equal abstractions give equal substituted bodies for every replacement.
This is the representative-independence equation needed for beta contraction,
including same binders, shadowing, and replacements with free binder atoms. -/
theorem subst_eq_of_lam_eq (a b : α) (t u s : Term α) (h : lam a t = lam b u) :
    t[a := s] = u[b := s] := by
  have hb : b # lam a t := by
    rw [h]
    exact fresh_term_lam_of_eq b u
  rw [subst_rename a b t s hb, (lam_eq_iff_at_fresh hb).mp h]

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
