import Instances.LambdaCalculus.Substitution

/-!
# Lambda interface consumers

These examples use only quotient-term operations and their public equations.
`FreshBinders` records an entire presentation whose nested binders avoid an
external nominal parameter and all previously chosen binders along their scope.
-/

namespace LambdaInterfaceExamples

open Nominal.Core Nominal.Set LambdaCalculus LambdaCalculus.Term

universe u
variable {α : Type u} [Name α] {X : Type u} [Nominal α X]

/-- A certificate of a presentation with fresh, pairwise distinct binders along
each path. The body certificate records the newly chosen binder in its context. -/
inductive FreshBinders (external : X) : Finset α → Term α → Prop where
  | var (A : Finset α) (a : α) : FreshBinders external A (var a)
  | app {A : Finset α} {t s : Term α} :
      FreshBinders external A t → FreshBinders external A s →
      FreshBinders external A (app t s)
  | lam {A : Finset α} {a : α} {t : Term α} :
      a # external → a ∉ A → FreshBinders external (insert a A) t →
      FreshBinders external A (lam a t)

/-- The fixed `external` occurs in the predicate itself: no equivariance
hypothesis on that predicate is required. At a nested lambda, the induction
hypothesis is used at the larger context containing its enclosing binder. -/
theorem freshBinders (external : X) (t : Term α) (A : Finset α) :
    FreshBinders external A t := by
  have all := strong_ind (Z := X × Finset α)
    (P := fun t z => z.1 = external → FreshBinders external z.2 t)
    (hVar := fun a z _ => FreshBinders.var z.2 a)
    (hApp := fun _ _ z ih₁ ih₂ hext =>
      FreshBinders.app (ih₁ z hext) (ih₂ z hext))
    (hLam := fun a t z ha ih hext => by
      have hparts := fresh_prod_right.mp ha
      refine FreshBinders.lam (hext ▸ hparts.1)
        (fresh_atom_finset.mp hparts.2) ?_
      exact ih (external, insert a z.2) rfl)
  exact all t (external, A) rfl

/-- A syntax view whose lambda alternative avoids a caller-selected finite set.
The simpler finset induction interface supplies precisely that condition. -/
theorem freshConstructorView (A : Finset α) (t : Term α) :
    (∃ a, t = var a) ∨ (∃ u v, t = app u v) ∨
      (∃ a u, a ∉ A ∧ t = lam a u) := by
  induction t using strong_ind_finset A with
  | hVar a => exact Or.inl ⟨a, rfl⟩
  | hApp u v _ _ => exact Or.inr (Or.inl ⟨u, v, rfl⟩)
  | hLam a u ha _ => exact Or.inr (Or.inr ⟨a, u, ha, rfl⟩)

/-- Substitution beneath a fresh binder may leave the replaced atom free in the
replacement; the replacement is deliberately open. -/
theorem openReplacement (a b : α) (hab : a ≠ b) :
    (lam b (var a))[a := var a] = lam b (var a) := by
  rw [subst_lam b (var a) a (var a)]
  · simp
  · simp [Ne.symm hab]

/-- An occurrence beneath its own binder is shadowed, for any replacement. -/
theorem shadowedVariable (a : α) (s : Term α) :
    (lam a (lam a (var a)))[a := s] = lam a (lam a (var a)) := by
  exact subst_fresh a _ s (fresh_term_lam_of_eq _ _)

/-- The replacement contains the old binder freely, so substituting directly
under that binder would capture it. Renaming first preserves its free occurrence. -/
theorem captureAvoidance (a b c : α) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    (lam b (var a))[a := var b] = lam c (var b) := by
  rw [subst_lam_rename b c (var a) a (var b) (by simpa using hca)]
  have hswap : swap b c • var a = var a := by
    simp [hab, Ne.symm hca]
  rw [hswap, subst_lam c (var a) a (var b) (by simp [hca, hcb])]
  simp

/-- Both binder names occur freely in the replacement. The contraction equation
still holds: neither old nor new binder must be fresh for the replacement. -/
theorem contractionWithOpenReplacement (a b : α) :
    (var a)[a := app (var a) (var b)] =
      (swap a b • var a)[b := app (var a) (var b)] ∧
    ¬ a # app (var a) (var b) ∧ ¬ b # app (var a) (var b) := by
  refine ⟨subst_rename a b (var a) (app (var a) (var b))
    (by simp), ?_, ?_⟩ <;> simp

/-- Compatibility for arbitrary alpha-equivalent lambda terms, expressed solely
through their equality and without imposing any condition on the replacement. -/
theorem equalLambdasContractEqually (a b : α) (t u s : Term α)
    (h : lam a t = lam b u) : t[a := s] = u[b := s] :=
  subst_eq_of_lam_eq a b t u s h

/-- Choosing the existing binder is supported even when it occurs in the body. -/
theorem sameBinderContraction (a : α) (t s : Term α) :
    t[a := s] = (swap a a • t)[a := s] :=
  subst_rename a a t s (fresh_term_lam_of_eq a t)

theorem renameBySubstitution (a b : α) (t : Term α) (hb : b # lam a t) :
    t[a := var b] = swap a b • t :=
  subst_var_eq_swap a b t hb

theorem substitutionIdentity (t : Term α) (a : α) : t[a := var a] = t := by
  simp

end LambdaInterfaceExamples

-- Fail the client build on admissions or additional axioms, including in the
-- public results consumed here. Standard classical Lean foundations are allowed.
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "LambdaInterfaceExamples." ||
        name.toString.startsWith "LambdaCalculus." then
      let axioms ← collectAxioms name
      let extra := axioms.filter fun a =>
        a != `propext && a != `Classical.choice && a != `Quot.sound
      unless extra.isEmpty do
        throwError "{name}: unexpected axioms {extra}"
