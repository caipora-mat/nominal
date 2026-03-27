import Instances.LambdaCalculus.Basic

/-!
# Strong Structural Induction for Lambda Terms

This file proves the strong structural induction principle for `Term α`,
the nominal quotient of raw lambda terms.

## Strong structural induction

The main induction principle for `Term α`. Given a property `P : Term α → Z → Prop`
(where `Z` is any nominal set serving as the induction "context"), we can prove
`∀ t z, P t z` by supplying:

- `hVar`: `P` holds for variables.
- `hApp`: if `P` holds for both subterms (at *all* contexts), it holds for the
  application.
- `hLam`: if `P` holds for the body (at *all* contexts) **and** the binder `a` is
  fresh for the context `z`, then `P` holds for `lam a t`.

The freshness side-condition `a # z` in `hLam` is the crucial feature. It gives
Barendregt's variable convention "for free": the bound variable can always be
assumed distinct from any finite set of names you're reasoning about.

### Why this works without an alpha-compatibility hypothesis

In constructive settings (e.g. Copello et al. 2016 in Agda), a similar principle
requires proving that `P` is invariant under alpha-equivalence. In our setting,
`Term α` is a quotient, so binder renaming produces a *propositionally equal*
term. Any predicate on `Term α` automatically respects this equality.

### Proof strategy

1. Strengthen the claim to `∀ (t : LamTerm α) (π : FinitePerm α) (z : Z), P ⟦π • t⟧ z`.
2. Prove the strengthened claim by structural recursion on `t`. In the lam case,
   pick `b # (z, ⟦π • t⟧)`, rename the binder via `term_lam_eq_iff`, and recurse
   at the composed permutation `swap (π • a) b * π`.
3. Conclude by setting `π = 1`.
-/

namespace LambdaCalculus

open Nominal.Core Nominal.Set NameAbs

universe u

variable {α : Type u} [Name α]

namespace Term

/-- Strengthened induction: for all permuted representatives `⟦π • t⟧`. -/
theorem strong_indperm {Z : Type u} [Nominal α Z]
    {P : Term α → Z → Prop}
    (hVar : ∀ a z, P (Term.var a) z)
    (hApp : ∀ t₁ t₂ z, (∀ d, P t₁ d) → (∀ d, P t₂ d) → P (Term.app t₁ t₂) z)
    (hLam : ∀ a t z, a # z → (∀ d, P t d) → P (Term.lam a t) z)
    (t : LamTerm α) (π : FinitePerm α) (z : Z) : P ⟦π • t⟧ z := by
  cases t with
  | var a => simp only [LamTerm.smul_var, PermType.atoms_smul, var_mk]; exact hVar (π • a) z
  | app t s =>
    simp only [LamTerm.smul_app, app_mk]
    exact hApp ⟦π • t⟧ ⟦π • s⟧ z
      (fun d ↦ strong_indperm hVar hApp hLam t π d)
      (fun d ↦ strong_indperm hVar hApp hLam s π d)
  | lam r =>
    obtain ⟨a, t⟩ := r
    change P (Term.lam (π • a) ⟦π • t⟧) z
    -- Pick b # (z, ⟦π • t⟧)
    choose_fresh b from z (⟦π • t⟧ : Term α)
    -- Rename binder: Term.lam (π • a) ⟦π • t⟧ = Term.lam b (swap (π • a) b • ⟦π • t⟧)
    have hrename : Term.lam (π • a) ⟦π • t⟧ = Term.lam b (swap (π • a) b • ⟦π • t⟧) := by
      rw [term_lam_eq_iff]; exact NameAbs.abs_eq_swap bFresh2
    rw [hrename]
    -- Now apply hLam with b # z; the IH comes from the recursive call at swap (π • a) b * π
    refine hLam b (swap (π • a) b • ⟦π • t⟧) z bFresh1 (fun d ↦ ?_)
    -- swap (π • a) b • ⟦π • t⟧ = ⟦(swap (π • a) b * π) • t⟧
    have : swap (π • a) b • (⟦π • t⟧ : Term α) = ⟦(swap (π • a) b * π) • t⟧ := by simp [mul_smul]
    rw [this]
    exact strong_indperm hVar hApp hLam t (swap (π • a) b * π) d

/-- Strong structural induction for `Term α`. In the lambda case, the binder
may be assumed fresh for the induction context `z : Z`.

See §9 above for the proof strategy and comparison with constructive approaches. -/
@[elab_as_elim]
theorem strong_ind {Z : Type u} [Nominal α Z]
    {P : Term α → Z → Prop}
    (hVar : ∀ a z, P (Term.var a) z)
    (hApp : ∀ t₁ t₂ z, (∀ d, P t₁ d) → (∀ d, P t₂ d) → P (Term.app t₁ t₂) z)
    (hLam : ∀ a t z, a # z → (∀ d, P t d) → P (Term.lam a t) z)
    : ∀ (t : Term α) (z : Z), P t z := by
  intro t z
  induction t using Quotient.ind with
  | _ t =>
    have := strong_indperm hVar hApp hLam t 1 z
    simp only [one_smul] at this
    exact this

/-- Strong induction parametrized by a finite set of names to avoid.
A simplified form of `strong_ind` where the context is a `Finset α`:
in the lambda case, the binder can be assumed outside the avoidance set `A`. -/
@[elab_as_elim]
theorem strong_ind_finset (A : Finset α)
    {P : Term α → Prop}
    (hVar : ∀ a, P (Term.var a))
    (hApp : ∀ t₁ t₂, P t₁ → P t₂ → P (Term.app t₁ t₂))
    (hLam : ∀ a t, a ∉ A → P t → P (Term.lam a t))
    : ∀ (t : Term α), P t := by
  intro t
  exact strong_ind (Z := Finset α)
    (P := fun t z ↦ z = A → P t)
    (hVar := fun a _ _ ↦ hVar a)
    (hApp := fun t₁ t₂ _ ih₁ ih₂ heq ↦ hApp t₁ t₂ (ih₁ A rfl) (ih₂ A rfl))
    (hLam := fun a t z ha ih heq ↦ hLam a t (fresh_atom_finset.mp (heq ▸ ha)) (ih A rfl))
    t A rfl

/-!
## Recursion combinators (separate files)

The recursion combinators and substitution are developed in companion files:

- **`Instances/LambdaCalculus/Recursion.lean`** — Urban's inductive relation approach.
- TODO **`Instances/Pitts.lean`** — Pitts' `ĝ` construction with a permutation parameter.
- **`Instances/LambdaCalculus/Substitution.lean`** — Capture-avoiding substitution.

See those files for the discussion of why direct `liftFCB`-based recursion fails
for the parametric case and how each approach resolves the equivariance obstacle.
-/

end Term

end LambdaCalculus
