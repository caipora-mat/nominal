/-
Copyright (c) 2026 Nominal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nominal contributors
-/
import Instances
import Lean.Util.CollectAxioms

/-!
# Consumers of fresh reduction induction and inversion

The example-only trees below record a derivation whose binders avoid an ambient
finite set and all enclosing binders. Their construction uses recursive
hypotheses at an enlarged context beneath each lambda, so a fixed-context
induction principle would not suffice. These are certificates for testing the
public principles, not new reduction relations in the supported lambda API.
-/

namespace LambdaFreshReductionExamples

open Nominal.Core Nominal.Set LambdaCalculus LambdaCalculus.Term

universe u v
variable {α : Type u} [Name α]

/-- A beta derivation presented with fresh, pairwise distinct enclosing binders. -/
inductive FreshBetaTree : Finset α → Term α → Term α → Prop where
  | beta (A : Finset α) (a : α) (t s : Term α) (ha : a ∉ A) (hs : a # s) :
      FreshBetaTree A (app (lam a t) s) (t[a := s])
  | app_left {A : Finset α} {t t' : Term α} (s : Term α)
      (h : FreshBetaTree A t t') : FreshBetaTree A (app t s) (app t' s)
  | app_right {A : Finset α} (t : Term α) {s s' : Term α}
      (h : FreshBetaTree A s s') : FreshBetaTree A (app t s) (app t s')
  | lam {A : Finset α} (a : α) {t t' : Term α} (ha : a ∉ A)
      (h : FreshBetaTree (insert a A) t t') : FreshBetaTree A (lam a t) (lam a t')

/-- A parallel derivation with the same nested-binder convention. The beta
case records both recursive premises and freshness for both arguments. -/
inductive FreshParallelTree : Finset α → Term α → Term α → Prop where
  | var (A : Finset α) (a : α) : FreshParallelTree A (var a) (var a)
  | app {A : Finset α} {t t' s s' : Term α}
      (ht : FreshParallelTree A t t') (hs : FreshParallelTree A s s') :
      FreshParallelTree A (app t s) (app t' s')
  | lam {A : Finset α} (a : α) {t t' : Term α} (ha : a ∉ A)
      (h : FreshParallelTree (insert a A) t t') :
      FreshParallelTree A (lam a t) (lam a t')
  | beta {A : Finset α} (a : α) {t t' s s' : Term α}
      (ha : a ∉ A) (has : a # s) (has' : a # s')
      (ht : FreshParallelTree (insert a A) t t') (hs : FreshParallelTree A s s') :
      FreshParallelTree A (app (lam a t) s) (t'[a := s'])

/-- Each lambda IH is used at `insert a A`, not the handler's original `A`. -/
theorem betaTree {t t' : Term α} (h : Beta t t') (A : Finset α) :
    FreshBetaTree A t t' := by
  apply Beta.strong_ind (P := fun t t' A => FreshBetaTree A t t')
    (hBeta := fun a t s A ha hs => .beta A a t s (fresh_atom_finset.mp ha) hs)
    (hAppLeft := fun _ _ s A _ ih => .app_left s (ih A))
    (hAppRight := fun t _ _ A _ ih => .app_right t (ih A))
    (hLam := fun a _ _ A _ ha ih => .lam a (fresh_atom_finset.mp ha) (ih (insert a A)))
    h A

/-- The contraction body IH also admits an enlarged context, while the argument
IH is used at the ambient context because the binder does not scope over it. -/
theorem parallelTree {t t' : Term α} (h : Parallel t t') (A : Finset α) :
    FreshParallelTree A t t' := by
  apply Parallel.strong_ind (P := fun t t' A => FreshParallelTree A t t')
    (hVar := fun a A => .var A a)
    (hApp := fun _ _ _ _ A _ _ iht ihs => .app (iht A) (ihs A))
    (hLam := fun a _ _ A _ ha ih => .lam a (fresh_atom_finset.mp ha) (ih (insert a A)))
    (hBeta := fun a _ _ _ _ A _ _ ha hs hs' iht ihs =>
      .beta a (fresh_atom_finset.mp ha) hs hs' (iht (insert a A)) (ihs A))
    h A

/-- An arbitrary atom predicate may be captured by the motive; no nominal
instance, equivariance, or finite support is required for `q`. The fresh binder
fact removes the bound-name alternative, and both beta-premise IHs are needed. -/
theorem parallelFreshWhen (q : α → Prop) {t t' : Term α} (h : Parallel t t')
    (x : α) (hq : q x) (hx : x # t) : x # t' := by
  apply Parallel.strong_ind (P := fun t t' x => q x → x # t → x # t')
    (hVar := fun _ _ _ hx => hx)
    (hApp := fun _ _ _ _ x _ _ iht ihs hq hx =>
      fresh_term_app _ _ _ |>.mpr
        ⟨iht x hq (fresh_term_app _ _ _ |>.mp hx).1,
         ihs x hq (fresh_term_app _ _ _ |>.mp hx).2⟩)
    (hLam := fun a t _ x _ ha ih hq hx => by
      have hxa : x ≠ a := (fresh_atoms a x |>.mp ha).symm
      have hxt : x # t := (fresh_term_lam x a t |>.mp hx).resolve_left hxa
      exact fresh_term_lam_of_fresh _ _ _ (ih x hq hxt))
    (hBeta := fun a t _ s _ x _ _ ha _ _ iht ihs hq hx => by
      obtain ⟨hxt, hxs⟩ := fresh_term_app _ _ _ |>.mp hx
      have hxa : x ≠ a := (fresh_atoms a x |>.mp ha).symm
      have hxt : x # t := (fresh_term_lam x a t |>.mp hxt).resolve_left hxa
      exact subst_fresh_of_fresh _ _ _ _ (iht x hq hxt) (ihs x hq hxs))
    h x hq hx

/-- The displayed source repeats `a` as a binder twice. The certificate instead
presents both binders fresh for external `x,r` and distinct from one another. -/
theorem nestedBetaBinders (a x : α) (r s : Term α) :
    FreshBetaTree (insert x (supp r))
      (lam a (lam a (app (lam a (var a)) s))) (lam a (lam a s)) := by
  apply betaTree
  exact Beta.lam a (Beta.lam a (by simpa using Beta.beta a (var a) s))

/-- Both recursive contraction premises are themselves genuine contractions;
the certificate exercises freshness and both IHs, with external atom/term data. -/
theorem parallelBodyAndArgument (a b c d x : α) (r : Term α) :
    FreshParallelTree (insert x (supp r))
      (app (lam a (app (lam b (var b)) (var a))) (app (lam c (var c)) (var d)))
      (var d) := by
  apply parallelTree
  have ht : Parallel (app (lam b (var b)) (var a)) (var a) := by
    simpa using Parallel.beta b (Parallel.var b) (Parallel.var a)
  have hs : Parallel (app (lam c (var c)) (var d)) (var d) := by
    simpa using Parallel.beta c (Parallel.var c) (Parallel.var d)
  simpa using Parallel.beta a ht hs

/-- The finite-set wrapper also supports a predicate depending on a fixed atom.
Freshness for the rule binder is what lets each lambda case use its body IH. -/
theorem betaFreshViaFinset {t t' : Term α} (h : Beta t t')
    (x : α) (hx : x # t) : x # t' := by
  apply Beta.strong_ind_finset {x} (P := fun t t' => x # t → x # t')
    (hBeta := fun a t s ha _ hx => by
      obtain ⟨hxt, hxs⟩ := fresh_term_app _ _ _ |>.mp hx
      have hxa : x ≠ a := (Finset.notMem_singleton.mp ha).symm
      exact subst_fresh_of_fresh _ _ _ _
        ((fresh_term_lam x a t |>.mp hxt).resolve_left hxa) hxs)
    (hAppLeft := fun _ _ _ _ ih hx => by
      obtain ⟨ht, hs⟩ := fresh_term_app _ _ _ |>.mp hx
      exact fresh_term_app _ _ _ |>.mpr ⟨ih ht, hs⟩)
    (hAppRight := fun _ _ _ _ ih hx => by
      obtain ⟨ht, hs⟩ := fresh_term_app _ _ _ |>.mp hx
      exact fresh_term_app _ _ _ |>.mpr ⟨ht, ih hs⟩)
    (hLam := fun a t _ _ ha ih hx => by
      have hxa : x ≠ a := (Finset.notMem_singleton.mp ha).symm
      exact fresh_term_lam_of_fresh _ _ _
        (ih ((fresh_term_lam x a t |>.mp hx).resolve_left hxa)))
    h hx

/-- A nontrivial beta step is displayed with genuinely different endpoint
binders, then inverted at a common binder fresh for external atom/term data.
The target presentation is alpha-equivalent to `lam a s`. -/
theorem alphaRenamedBetaInversion (a x : α) (r s : Term α) :
    ∃ b c, b ≠ a ∧ c # (x, r) ∧
      Beta (lam a (app (lam a (var a)) s)) (lam b (swap a b • s)) ∧
      Beta (swap a c • app (lam a (var a)) s) (swap b c • (swap a b • s)) := by
  choose_fresh b from a s
  have hstep : Beta (lam a (app (lam a (var a)) s)) (lam b (swap a b • s)) := by
    rw [← lam_eq_swap (fresh_term_lam_of_fresh b a s bFresh2)]
    exact Beta.lam a (by simpa using Beta.beta a (var a) s)
  choose_fresh c from (x, r) (lam a (app (lam a (var a)) s))
  exact ⟨b, c, fresh_atoms b a |>.mp bFresh1, cFresh1, hstep,
    (Beta.lam_iff_common_fresh cFresh2 (hstep.fresh cFresh2)).mp hstep⟩

/-- Parallel inversion aligns alpha-equivalent identity presentations at an
externally fresh binder. Their originally displayed binders are distinct. -/
theorem alphaRenamedParallelInversion (a x : α) (r : Term α) :
    ∃ b c, b ≠ a ∧ c # (x, r) ∧
      Parallel (swap a c • var a) (swap b c • var b) := by
  choose_fresh b from a
  have heq : lam a (var a) = lam b (var b) := by
    simpa using (lam_eq_swap (a := a) (b := b) (t := var a) (by simp))
  have hstep : Parallel (lam a (var a)) (lam b (var b)) := by
    rw [← heq]
  choose_fresh c from (x, r) (lam a (var a))
  exact ⟨b, c, fresh_atoms b a |>.mp bFresh1, cFresh1,
    (Parallel.lam_iff_common_fresh cFresh2 (hstep.fresh cFresh2)).mp hstep⟩

/-- Fresh inversion can be iterated under binders using a nominal parameter in
an independent universe. The inner binder also avoids the newly chosen outer
binder, while the result exposes the actual nested premise derivation. -/
theorem nestedParallelInversion {X : Type v} [Nominal α X] (z : X)
    (a b : α) (t u : Term α) (h : Parallel (lam a (lam b t)) u) :
    ∃ c d v w, c # z ∧ d # (z, c) ∧
      lam a (lam b t) = lam c (lam d v) ∧
      u = lam c (lam d w) ∧ Parallel v w := by
  obtain ⟨c, v, w, hc, hsource, hbody, htarget⟩ := (Parallel.lam_iff_fresh z).mp h
  have hcfresh : c # lam a (lam b t) := by
    rw [hsource]
    exact fresh_term_lam_of_eq _ _
  have hv := (lam_eq_iff_at_fresh hcfresh).mp hsource
  simp only [smul_lam] at hv
  rw [← hv] at hbody
  obtain ⟨d, v', w', hd, hsource', hbody', htarget'⟩ :=
    (Parallel.lam_iff_fresh (z, c)).mp hbody
  refine ⟨c, d, v', w', hc, hd, ?_, ?_, hbody'⟩
  · exact hsource.trans (congrArg (lam c) (hv.symm.trans hsource'))
  · exact htarget.trans (congrArg (lam c) htarget')

/-- A chosen common binder may occur freely in the bodies it binds. -/
theorem sameBinderInBody (a : α) :
    Parallel (lam a (var a)) (lam a (var a)) ↔ Parallel (var a) (var a) :=
  Parallel.lam_lam_iff

/-- Fixed-binder application inversion allows the redex argument to contain
that binder freely; freshness is required only for the head abstraction. -/
theorem sameBinderInArgument (a : α) : Parallel (app (lam a (var a)) (var a)) (var a) := by
  apply (Parallel.app_iff_at_fresh (fresh_term_lam_of_eq a (var a))).mpr
  exact Or.inr ⟨var a, var a, var a, rfl, Parallel.refl _, Parallel.refl _, by simp⟩

/-- Omega witnesses genuine overlap: the same endpoints satisfy both branches
of fresh parallel application inversion, so those branches cannot be exclusive. -/
theorem parallelApplicationAlternativesOverlap (a : α) :
    let d := lam a (app (var a) (var a))
    (∃ t' s', Parallel d t' ∧ Parallel d s' ∧ app d d = app t' s') ∧
      (∃ u u' s', d = lam a u ∧ Parallel u u' ∧ Parallel d s' ∧
        app d d = u'[a := s']) := by
  dsimp
  constructor
  · exact ⟨_, _, Parallel.refl _, Parallel.refl _, rfl⟩
  · exact ⟨_, _, _, rfl, Parallel.refl _, Parallel.refl _, by simp⟩

end LambdaFreshReductionExamples

-- Check every consumer, including example certificates, against the standard
-- classical foundations. The public lambda API is audited in LambdaReduction.
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "LambdaFreshReductionExamples." then
      let axioms ← collectAxioms name
      let extra := axioms.filter fun a =>
        a != `propext && a != `Classical.choice && a != `Quot.sound
      unless extra.isEmpty do
        throwError "{name}: unexpected axioms {extra}"
