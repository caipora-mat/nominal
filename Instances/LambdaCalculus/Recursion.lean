import Instances.LambdaCalculus.Induction

/-!
# Recursion via Urban's Inductive Relation

This file defines a general recursion combinator `recNoContext` on the nominal quotient
`Term α`, following Urban's approach from *Nominal Techniques in Isabelle/HOL*
(JAR 2008, Theorem 3).

## The problem: recursion on alpha-equivalence classes

A direct structural recursion on `LamTerm α` (the raw term type) is easy to define
but hard to quotient. Proving that the recursion respects alpha-equivalence requires
an **equivariance** property:

    `swap aᵢ c • rec z tᵢ = rec z' (swap aᵢ c • tᵢ)`

connecting a permutation of the *result* to the recursion on a permuted *input*.
When the constructor functions (`NFun`s) have non-empty support, this fails for swaps
involving names in the support — precisely the swaps needed for well-definedness.

Two solutions exist in the literature:

* **Pitts (JACM 2006)**: strengthen the recursion to `ĝ : LamTerm → (Perm →_fs Y)`,
  carrying a permutation parameter that absorbs the problematic swaps.
* **Urban (JAR 2008)**: define the recursion as an *inductive relation* on the
  quotient `Term α`, then prove totality and functionality, and extract the function
  via `Classical.choose`.

We follow Urban's approach. Working on the quotient is the key insight: since equal
terms in `Term α` are propositionally equal, any predicate on `Term α` automatically
respects alpha-equivalence. No equivariance proof is needed.

## Structure of this file

1. `RecRel` — the inductive relation on `Term α`, parameterised by three `NFun`s
   (`fᵥ`, `fₐ`, `f_L`) and a support set `A`. The lam rule requires `a # A`.
2. Totality — every term has a value, by `strong_ind`.
3. Inversion lemmas — for pattern-matching on quotient-indexed derivations.
4. Equivariance — swaps fixing `A` preserve `RecRel` derivations (Urban's Lemma 13).
5. Uniqueness — at most one value per term (Urban's Lemma 14).
6. Extraction — `recNoContext` via `Classical.choose`, with computation lemmas.

## References

* Urban, *Nominal Techniques in Isabelle/HOL*, JAR 2008, Theorem 3 (equation 23)
* Urban, *Nominal Techniques in Isabelle/HOL*, JAR 2008, Lemma 13 (equivariance)
* Urban, *Nominal Techniques in Isabelle/HOL*, JAR 2008, Lemma 14 (totality + uniqueness)
* Pitts, *Alpha-Structural Recursion and Induction*, JACM 2006, Theorem 4.1
-/

namespace LambdaCalculus

open Nominal.Core Nominal.Set NameAbs

universe u

variable {α : Type u} [Name α]

namespace Term

/-!
## §1. The recursion relation

Following Urban's equation (23), we define an inductive relation `RecRel` on the
quotient `Term α`. The three parameters `fᵥ`, `fₐ`, `f_L` are finitely-supported
functions (`NFun`) for the variable, application, and lambda cases respectively.
The support set `A` bounds the supports of all three, and the lam rule requires
the binder `a` to be fresh for `A`.

Since the relation lives on the quotient, there is no alpha-equivalence obligation:
equal terms in `Term α` are propositionally equal, so any predicate on `Term α`
automatically respects alpha-equivalence. This is the central advantage of Urban's
approach.
-/

/-- The recursion relation for the context-free combinator.

`RecRel fᵥ fₐ f_L A t y` means "the recursion applied to `t` yields `y`".
Corresponds to Urban's `rec_{f₁,f₂,f₃}` relation (equation 23). -/
inductive RecRel {Y : Type u} [Nominal α Y]
    (fᵥ : NFun α α Y) (fₐ : NFun α (Y × Y) Y) (f_L : NFun α (α × Y) Y) (A : Finset α)
    : Term α → Y → Prop where
  | var (a : α) : RecRel fᵥ fₐ f_L A (Term.var a) (fᵥ a)
  | app {t₁ t₂ : Term α} {y₁ y₂ : Y} :
      RecRel fᵥ fₐ f_L A t₁ y₁ → RecRel fᵥ fₐ f_L A t₂ y₂ →
      RecRel fᵥ fₐ f_L A (Term.app t₁ t₂) (fₐ (y₁, y₂))
  | lam {a : α} {t : Term α} {y : Y} :
      a # A → RecRel fᵥ fₐ f_L A t y →
      RecRel fᵥ fₐ f_L A (Term.lam a t) (f_L (a, y))

/-!
## §2. Totality

Every `Term α` has at least one value related to it by `RecRel`. This is the
"existential" part of Urban's Lemma 14.

*Proof.* By `strong_ind_finset` on `Term α` with avoidance set `A`. The key
is that `strong_ind_finset` in the lam case provides a binder `a` with `a ∉ A`,
giving exactly the side-condition `a # A` required by `RecRel.lam`.
The var and app cases are immediate from the constructors and the IHs.
-/

theorem RecRel.total {Y : Type u} [Nominal α Y]
    (fᵥ : NFun α α Y)
    (fₐ : NFun α (Y × Y) Y)
    (f_L : NFun α (α × Y) Y)
    (A : Finset α)
    (_hᵥ : supp fᵥ ⊆ A) (_hₐ : supp fₐ ⊆ A) (_h_L : supp f_L ⊆ A)
    (_hFCB : ∀ (a : α) (y : Y), a # A → a # f_L (a, y))
    (t : Term α) : ∃ y, RecRel fᵥ fₐ f_L A t y := by
  induction t using strong_ind_finset A with
  | hVar a => exact ⟨fᵥ a, .var a⟩
  | hApp _ _ ih₁ ih₂ =>
    obtain ⟨y₁, h₁⟩ := ih₁; obtain ⟨y₂, h₂⟩ := ih₂
    exact ⟨fₐ (y₁, y₂), .app h₁ h₂⟩
  | hLam a _ ha ih =>
    obtain ⟨y, h⟩ := ih
    exact ⟨f_L (a, y), .lam (fresh_atom_finset.mpr ha) h⟩

/-!
## §3. Inversion lemmas and constructor discrimination

`RecRel` is indexed by `Term α` (a quotient type), so Lean's `cases` tactic cannot
directly invert a derivation at a specific constructor. We prove inversion lemmas
using `generalize` + `induction` on the derivation, discharging impossible branches
via `Quotient.exact` and raw-term constructor discrimination.

The discrimination lemmas `var_ne_app`, `var_ne_lam`, `app_ne_lam` establish that
the three `Term` constructors are pairwise distinguishable on the quotient. These are
proved by reducing to raw terms via `Quotient.exact` and case-splitting on the
(impossible) alpha-equivalence derivation.
-/

theorem var_ne_app (a : α) (t₁ t₂ : Term α) : Term.var a ≠ Term.app t₁ t₂ := by
  induction t₁, t₂ using Quotient.ind₂ with | _ s₁ s₂ =>
    intro h; have := Quotient.exact h; cases this

theorem var_ne_lam (a : α) (b : α) (t : Term α) : Term.var a ≠ Term.lam b t := by
  induction t using Quotient.ind with | _ s =>
    intro h; have := Quotient.exact h; cases this

theorem app_ne_lam (t₁ t₂ : Term α) (a : α) (s : Term α) :
    Term.app t₁ t₂ ≠ Term.lam a s := by
  induction t₁, t₂ using Quotient.ind₂ with | _ r₁ r₂ =>
    induction s using Quotient.ind with | _ r =>
      intro h; have := Quotient.exact h; cases this

/-- Inversion for `var`: the only `RecRel` derivation at `var a` uses the `var` rule. -/
theorem RecRel.inv_var {Y : Type u} [Nominal α Y]
    (fᵥ : NFun α α Y) (fₐ : NFun α (Y × Y) Y) (f_L : NFun α (α × Y) Y)
    (A : Finset α) {a : α} {y : Y}
    (h : RecRel fᵥ fₐ f_L A (Term.var a) y) : y = fᵥ a := by
  generalize hteq : Term.var a = t' at h
  induction h with
  | var a' =>
    change ⟦LamTerm.var a⟧ = ⟦LamTerm.var a'⟧ at hteq
    have := AEq.var_iff.mp (Quotient.exact hteq)
    subst this; rfl
  | app _ _ _ _ => exact absurd hteq (var_ne_app _ _ _)
  | lam _ _ _ => exact absurd hteq (var_ne_lam _ _ _)

/-- Inversion for `app`: the only `RecRel` derivation at `app t₁ t₂` uses the `app` rule. -/
private theorem RecRel.inv_app {Y : Type u} [Nominal α Y]
    (fᵥ : NFun α α Y) (fₐ : NFun α (Y × Y) Y) (f_L : NFun α (α × Y) Y)
    (A : Finset α) {t₁ t₂ : Term α} {y : Y}
    (h : RecRel fᵥ fₐ f_L A (Term.app t₁ t₂) y) :
    ∃ y₁ y₂, RecRel fᵥ fₐ f_L A t₁ y₁ ∧ RecRel fᵥ fₐ f_L A t₂ y₂ ∧ y = fₐ (y₁, y₂) := by
  generalize hteq : Term.app t₁ t₂ = t' at h
  induction h with
  | var _ => exact absurd hteq.symm (var_ne_app _ _ _)
  | @app s₁ s₂ q₁ q₂ hs₁ hs₂ _ _ =>
    induction t₁, t₂ using Quotient.ind₂ with | _ r₁ r₂ =>
    induction s₁, s₂ using Quotient.ind₂ with | _ u₁ u₂ =>
    have haeq : (r₁ ◃ r₂) ≈α (u₁ ◃ u₂) := Quotient.exact hteq
    have ⟨haeq₁, haeq₂⟩ := AEq.app_iff.mp haeq
    have heq₁ : (⟦r₁⟧ : Term α) = ⟦u₁⟧ := Quotient.sound haeq₁
    have heq₂ : (⟦r₂⟧ : Term α) = ⟦u₂⟧ := Quotient.sound haeq₂
    exact ⟨q₁, q₂, heq₁ ▸ hs₁, heq₂ ▸ hs₂, rfl⟩
  | lam _ _ _ => exact absurd hteq (app_ne_lam _ _ _ _)

/-- Inversion for `lam`: the only `RecRel` derivation at `lam a t` uses the `lam` rule
(possibly with a different binder `b` and body `t'` such that `lam a t = lam b t'`). -/
private theorem RecRel.inv_lam {Y : Type u} [Nominal α Y]
    (fᵥ : NFun α α Y) (fₐ : NFun α (Y × Y) Y) (f_L : NFun α (α × Y) Y)
    (A : Finset α) {a : α} {t : Term α} {y : Y}
    (h : RecRel fᵥ fₐ f_L A (Term.lam a t) y) :
    ∃ b t' r, b # A ∧ RecRel fᵥ fₐ f_L A t' r ∧ Term.lam a t = Term.lam b t' ∧ y = f_L (b, r) := by
  generalize hteq : Term.lam a t = t'' at h
  induction h with
  | var _ => exact absurd hteq.symm (var_ne_lam _ _ _)
  | app _ _ _ _ => exact absurd hteq.symm (app_ne_lam _ _ _ _)
  | @lam b s r hb hr _ =>
    exact ⟨b, s, r, hb, hr, rfl, rfl⟩

/-!
## §4. Equivariance for swaps fixing `A`

When `a, b # A`, the swap `(a b)` fixes all three NFuns (since their supports are
contained in `A`) and fixes `A` itself as a finset. Therefore, if `RecRel t y` then
`RecRel (swap a b • t) (swap a b • y)` — with the *same* NFuns and support set.

This is Urban's Lemma 13. The proof is by induction on the `RecRel` derivation. The
key technical step: for each NFun `F` with `supp F ⊆ A`, we show
`F (swap a b • x) = swap a b • F x` using the fact that the swap fixes `F`.
-/

theorem RecRel.swap_equiv {Y : Type u} [Nominal α Y]
    (fᵥ : NFun α α Y) (fₐ : NFun α (Y × Y) Y) (f_L : NFun α (α × Y) Y)
    (A : Finset α) (hᵥ : supp fᵥ ⊆ A) (hₐ : supp fₐ ⊆ A) (h_L : supp f_L ⊆ A)
    (_hFCB : ∀ (a : α) (y : Y), a # A → a # f_L (a, y))
    {a b : α} (ha : a # A) (hb : b # A)
    {t : Term α} {y : Y} (h : RecRel fᵥ fₐ f_L A t y) :
    RecRel fᵥ fₐ f_L A (swap a b • t) (swap a b • y) := by
  have freshA_a : ∀ {X : Type u} [Nominal α X] {F : X}, supp F ⊆ A → a # F := fun hF => fresh_of_supp_subset_finset hF ha
  have freshA_b : ∀ {X : Type u} [Nominal α X] {F : X}, supp F ⊆ A → b # F := fun hF => fresh_of_supp_subset_finset hF hb
  have nfun_equiv : ∀ {X W : Type u} [Nominal α X] [Nominal α W] (F : NFun α X W), supp F ⊆ A → ∀ x, F (swap a b • x) = swap a b • F x := by
    intro X W _ _ F hF x
    calc F (swap a b • x)
        _ = (swap a b • F) (swap a b • x) := by rw [fresh_swap (freshA_a hF) (freshA_b hF)]
        _ = swap a b • F x := NFun.smul_apply_smul ..
  have hA_fix : swap a b • A = A := fresh_swap ha hb
  induction h with
  | @var c =>
    simp only [smul_var, (nfun_equiv fᵥ hᵥ c).symm]; exact .var _
  | @app t₁ t₂ r₁ r₂ _ _ ih₁ ih₂ =>
    simp only [smul_app, (nfun_equiv fₐ hₐ (r₁, r₂)).symm]; exact .app ih₁ ih₂
  | @lam c t r hc hr ih =>
    simp only [smul_lam, (nfun_equiv f_L h_L (c, r)).symm]
    exact .lam (by rwa [← hA_fix, fresh_equivariant_iff]) ih

/-!
## §5. Uniqueness (functionality)

If `RecRel t y₁` and `RecRel t y₂`, then `y₁ = y₂`. This is the "uniqueness" part
of Urban's Lemma 14.

*Proof.* By induction on the first `RecRel` derivation, generalising over `y₂`.

- **var**: By `inv_var`, `y₂ = fᵥ a = y₁`.
- **app**: By `inv_app`, `y₂ = fₐ (r₂, s₂)` where `RecRel t₁ r₂` and `RecRel t₂ s₂`.
  The IHs give `r₁ = r₂` and `s₁ = s₂`.
- **lam** (the crux): We have `h₁ : RecRel (lam a t) (f_L (a, r))` with `a # A` and
  `RecRel t r`, and `inv_lam` of `h₂` gives `(b, t', r')` with `b # A`,
  `RecRel t' r'`, and `lam a t = lam b t'` on the quotient.

  The goal is `f_L (a, r) = f_L (b, r')`. This requires relating `r` (from `RecRel t`)
  to `r'` (from `RecRel t'`), where `t` and `t'` are alpha-equivalent bodies under
  different binders. The argument proceeds in stages:

  1. From `lam a t = lam b t'`, extract `⟪a⟫t = ⟪b⟫t'` in `NameAbs` via `term_lam_eq_iff`.
  2. Pick `c` fresh for `(A, a, t, b, t', r, r')` via `choose_fresh`.
  3. From the abstraction equality at `c`: `swap a c • t = swap b c • t'` via `abs_eq_mp_at`.
  4. Apply `swap_equiv` with `b, c # A` to get `RecRel (swap b c • t') (swap b c • r')`.
  5. Rewrite using step 3: `RecRel (swap a c • t) (swap b c • r')`.
  6. Apply `swap_equiv` backwards with `a, c # A` and `swap_smul_swap_smul`:
     `RecRel t (swap a c • swap b c • r')`.
  7. By the IH: `r = swap a c • swap b c • r'`, hence `swap a c • r = swap b c • r'`.
  8. From step 7 and `c` fresh: `⟪a⟫r = ⟪b⟫r'` via `abs_eq_of_swap`.
  9. Finally, `FCB_guarded_val_indep` gives `f_L (a, r) = f_L (b, r')`.
-/

theorem RecRel.unique {Y : Type u} [Nominal α Y]
    (fᵥ : NFun α α Y) (fₐ : NFun α (Y × Y) Y) (f_L : NFun α (α × Y) Y)
    (A : Finset α) (hᵥ : supp fᵥ ⊆ A) (hₐ : supp fₐ ⊆ A) (h_L : supp f_L ⊆ A)
    (hFCB : ∀ (a : α) (y : Y), a # A → a # f_L (a, y))
    {t : Term α} {y₁ y₂ : Y} (h₁ : RecRel fᵥ fₐ f_L A t y₁) (h₂ : RecRel fᵥ fₐ f_L A t y₂) :
    y₁ = y₂ := by
  induction h₁ generalizing y₂ with
  | var a => rw [RecRel.inv_var fᵥ fₐ f_L A h₂]
  | app _ _ ih₁ ih₂ =>
    obtain ⟨r₂, s₂, hr₂, hs₂, heq₂⟩ := RecRel.inv_app fᵥ fₐ f_L A h₂
    rw [heq₂, ih₁ hr₂, ih₂ hs₂]
  | @lam a t r ha_A hr ih =>
    obtain ⟨b, t', r', hb_A, hr', hlam_eq, heq₂⟩ := RecRel.inv_lam fᵥ fₐ f_L A h₂
    rw [heq₂]
    have habs : ⟪a⟫t = ⟪b⟫t' := term_lam_eq_iff.mp hlam_eq
    choose_fresh c from A a t b t' r r'
    have hc_att' : c # (a, t, b, t') :=
      fresh_prod_right.mpr ⟨cFresh2, fresh_prod_right.mpr ⟨cFresh3, fresh_prod_right.mpr ⟨cFresh4, cFresh5⟩⟩⟩
    have habs_c : swap a c • t = swap b c • t' := NameAbs.abs_eq_mp_at habs hc_att'
    have hse_r' := RecRel.swap_equiv fᵥ fₐ f_L A hᵥ hₐ h_L hFCB hb_A cFresh1 hr'
    rw [← habs_c] at hse_r'
    have hse_back := RecRel.swap_equiv fᵥ fₐ f_L A hᵥ hₐ h_L hFCB ha_A cFresh1 hse_r'
    rw [swap_smul_swap_smul] at hse_back
    have hswap_rr : swap a c • r = swap b c • r' := by
      rw [ih hse_back, swap_smul_swap_smul]
    have hc_arr' : c # (a, r, b, r') :=
      fresh_prod_right.mpr ⟨cFresh2, fresh_prod_right.mpr ⟨cFresh6, fresh_prod_right.mpr ⟨cFresh4, cFresh7⟩⟩⟩
    have habs_r : ⟪a⟫r = (⟪b⟫r' : NameAbs α Y) := NameAbs.abs_eq_of_swap hc_arr' hswap_rr
    exact NameAbs.FCB_guarded_val_indep f_L A h_L hFCB ha_A hb_A habs_r

/-!
## §6. Function extraction and computation lemmas

With totality and uniqueness in hand, we extract the recursion function via
`Classical.choose`. The computation lemmas follow a uniform pattern: construct the
`RecRel` witness using the appropriate rule, then apply uniqueness with
`recNoContext_spec` to conclude equality.
-/

/-- The context-free recursion combinator, defined as `Classical.choose (RecRel.total ...)`. -/
noncomputable def recNoContext
    {Y : Type u} [Nominal α Y]
    (fᵥ : NFun α α Y) (fₐ : NFun α (Y × Y) Y) (f_L : NFun α (α × Y) Y)
    (A : Finset α) (hᵥ : supp fᵥ ⊆ A) (hₐ : supp fₐ ⊆ A) (h_L : supp f_L ⊆ A)
    (hFCB : ∀ (a : α) (y : Y), a # A → a # f_L (a, y))
    : Term α → Y :=
  fun t => Classical.choose (RecRel.total fᵥ fₐ f_L A hᵥ hₐ h_L hFCB t)

private theorem recNoContext_spec
    {Y : Type u} [Nominal α Y]
    (fᵥ : NFun α α Y) (fₐ : NFun α (Y × Y) Y) (f_L : NFun α (α × Y) Y)
    (A : Finset α) (hᵥ : supp fᵥ ⊆ A) (hₐ : supp fₐ ⊆ A) (h_L : supp f_L ⊆ A)
    (hFCB : ∀ (a : α) (y : Y), a # A → a # f_L (a, y))
    (t : Term α) :
    RecRel fᵥ fₐ f_L A t (recNoContext fᵥ fₐ f_L A hᵥ hₐ h_L hFCB t) :=
  Classical.choose_spec (RecRel.total fᵥ fₐ f_L A hᵥ hₐ h_L hFCB t)

@[simp] theorem recNoContext_var
    {Y : Type u} [Nominal α Y]
    (fᵥ : NFun α α Y) (fₐ : NFun α (Y × Y) Y) (f_L : NFun α (α × Y) Y)
    (A : Finset α) (hᵥ : supp fᵥ ⊆ A) (hₐ : supp fₐ ⊆ A) (h_L : supp f_L ⊆ A)
    (hFCB : ∀ (a : α) (y : Y), a # A → a # f_L (a, y))
    (a : α) :
    recNoContext fᵥ fₐ f_L A hᵥ hₐ h_L hFCB (Term.var a) = fᵥ a := by
  exact RecRel.unique fᵥ fₐ f_L A hᵥ hₐ h_L hFCB
    (recNoContext_spec fᵥ fₐ f_L A hᵥ hₐ h_L hFCB (Term.var a))
    (RecRel.var a)

@[simp] theorem recNoContext_app
    {Y : Type u} [Nominal α Y]
    (fᵥ : NFun α α Y) (fₐ : NFun α (Y × Y) Y) (f_L : NFun α (α × Y) Y)
    (A : Finset α) (hᵥ : supp fᵥ ⊆ A) (hₐ : supp fₐ ⊆ A) (h_L : supp f_L ⊆ A)
    (hFCB : ∀ (a : α) (y : Y), a # A → a # f_L (a, y))
    (t₁ t₂ : Term α) :
    recNoContext fᵥ fₐ f_L A hᵥ hₐ h_L hFCB (Term.app t₁ t₂) =
      fₐ (recNoContext fᵥ fₐ f_L A hᵥ hₐ h_L hFCB t₁, recNoContext fᵥ fₐ f_L A hᵥ hₐ h_L hFCB t₂) := by
  exact RecRel.unique fᵥ fₐ f_L A hᵥ hₐ h_L hFCB
    (recNoContext_spec fᵥ fₐ f_L A hᵥ hₐ h_L hFCB (Term.app t₁ t₂))
    (RecRel.app (recNoContext_spec fᵥ fₐ f_L A hᵥ hₐ h_L hFCB t₁) (recNoContext_spec fᵥ fₐ f_L A hᵥ hₐ h_L hFCB t₂))

/-- Lambda equation (conditional): `a # A → rec (lam a t) = f_L (a, rec t)`.

The freshness condition `a # A` is not a restriction in practice: given any
`lam a t`, we can alpha-rename to a binder fresh for `A` (see `recNoContext_lam_rename`). -/
theorem recNoContext_lam
    {Y : Type u} [Nominal α Y]
    (fᵥ : NFun α α Y) (fₐ : NFun α (Y × Y) Y) (f_L : NFun α (α × Y) Y)
    (A : Finset α) (hᵥ : supp fᵥ ⊆ A) (hₐ : supp fₐ ⊆ A) (h_L : supp f_L ⊆ A)
    (hFCB : ∀ (a : α) (y : Y), a # A → a # f_L (a, y))
    (a : α) (t : Term α) (ha : a # A) :
    recNoContext fᵥ fₐ f_L A hᵥ hₐ h_L hFCB (Term.lam a t) =
      f_L (a, recNoContext fᵥ fₐ f_L A hᵥ hₐ h_L hFCB t) := by
  exact RecRel.unique fᵥ fₐ f_L A hᵥ hₐ h_L hFCB
    (recNoContext_spec fᵥ fₐ f_L A hᵥ hₐ h_L hFCB (Term.lam a t))
    (RecRel.lam ha (recNoContext_spec fᵥ fₐ f_L A hᵥ hₐ h_L hFCB t))

/-- Binder renaming: `b # t → rec (lam a t) = rec (lam b (swap a b • t))`.

A pure consequence of alpha-equivalence (`term_lam_eq_iff` + `abs_eq_swap`). -/
theorem recNoContext_lam_rename
    {Y : Type u} [Nominal α Y]
    (fᵥ : NFun α α Y) (fₐ : NFun α (Y × Y) Y) (f_L : NFun α (α × Y) Y)
    (A : Finset α) (hᵥ : supp fᵥ ⊆ A) (hₐ : supp fₐ ⊆ A) (h_L : supp f_L ⊆ A)
    (hFCB : ∀ (a : α) (y : Y), a # A → a # f_L (a, y))
    (a b : α) (t : Term α) (hb : b # t) :
    recNoContext fᵥ fₐ f_L A hᵥ hₐ h_L hFCB (Term.lam a t) =
      recNoContext fᵥ fₐ f_L A hᵥ hₐ h_L hFCB (Term.lam b (swap a b • t)) := by
  congr 1; rw [term_lam_eq_iff]; exact NameAbs.abs_eq_swap hb

end Term

end LambdaCalculus
