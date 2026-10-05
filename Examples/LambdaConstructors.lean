import Instances.LambdaCalculus.Basic

/-!
# Constructor and fresh-binder clients

This file deliberately imports only basic syntax. Constructor discrimination and
alpha-renaming must remain usable without the induction or iteration modules.
-/

namespace LambdaConstructorExamples

open Nominal.Core Nominal.Set LambdaCalculus LambdaCalculus.Term NameAbs

universe u
variable {α : Type u} [Name α]

theorem variableEquality {a b : α} (h : var a = var b) : a = b :=
  var_inj.mp h

theorem applicationEquality {t₁ t₂ s₁ s₂ : Term α}
    (h : app t₁ t₂ = app s₁ s₂) : t₁ = s₁ ∧ t₂ = s₂ :=
  app_inj.mp h

theorem sameBinder {a : α} {t s : Term α} (h : lam a t = lam a s) : t = s :=
  lam_inj.mp h

theorem distinctConstructors (a : α) (t s : Term α) :
    var a ≠ app t s ∧ var a ≠ lam a t ∧ app t s ≠ lam a t ∧
      app t s ≠ var a ∧ lam a t ≠ var a ∧ lam a t ≠ app t s := by
  simp

theorem abstractionEquality {a b : α} {t s : Term α}
    (h : (⟪a⟫t : NameAbs α (Term α)) = ⟪b⟫s) : lam a t = lam b s :=
  term_lam_eq_iff.mpr h

/-- The chosen atom is fresh for the whole abstraction, not necessarily its body.
In particular, choosing the original binder remains valid. -/
theorem originalBinder (a : α) (t : Term α) : ∃! s, lam a t = lam a s :=
  exists_lam_eq_at_fresh (fresh_term_lam_of_eq a t)

theorem chosenBinder {a c : α} {t s : Term α}
    (hc : c # lam a t) (h : lam a t = lam c s) : swap a c • t = s :=
  (lam_eq_iff_at_fresh hc).mp h

theorem commonBinder {a b c : α} {t s : Term α}
    (hc₁ : c # lam a t) (hc₂ : c # lam b s) (h : lam a t = lam b s) :
    swap a c • t = swap b c • s :=
  (lam_eq_iff_common_fresh hc₁ hc₂).mp h

/-- Equal abstractions can share a body and binder while avoiding any external
nominal parameter; no representative is exposed to the client. -/
theorem alignAvoiding {X : Type u} [Nominal α X] (external : X)
    {a b : α} {t s : Term α} (h : lam a t = lam b s) :
    ∃ c u, c # external ∧ lam a t = lam c u ∧ lam b s = lam c u := by
  choose_fresh c from external (lam a t)
  obtain ⟨u, hu, _⟩ := exists_lam_eq_at_fresh cFresh2
  exact ⟨c, u, cFresh1, hu, h.symm.trans hu⟩

theorem identityBinders (a b : α) : lam a (var a) = lam b (var b) := by
  simpa using (lam_eq_swap (a := a) (b := b) (t := var a)
    (by simp))

/-- The inner binder shadows the outer one. Both may be renamed independently,
including to distinct names, without any assumptions on those names. -/
theorem shadowing (a b c : α) :
    lam a (lam a (var a)) = lam b (lam c (var c)) := by
  calc
    lam a (lam a (var a)) = lam b (swap a b • lam a (var a)) :=
      lam_eq_swap (by simp)
    _ = lam b (lam b (var b)) := by simp
    _ = lam b (lam c (var c)) := congrArg (lam b) (identityBinders b c)

end LambdaConstructorExamples

-- Reject admissions and additional axioms in the Basic-only clients.
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "LambdaConstructorExamples." then
      let axioms ← collectAxioms name
      let extra := axioms.filter fun a =>
        a != `propext && a != `Classical.choice && a != `Quot.sound
      unless extra.isEmpty do
        throwError "{name}: unexpected axioms {extra}"
