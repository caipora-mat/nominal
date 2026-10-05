/-
Copyright (c) 2026 Nominal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nominal contributors
-/
import Instances
import Lean.Util.CollectAxioms

/-!
# From fresh names to Church–Rosser

The accompanying `docs/tutorial.md` explains this sequence of public-API clients.
Compile with `lake build Examples` or `lake env lean Examples/Tutorial.lean`.
No example opens a raw representative or the iterator's defining relation.
-/

namespace NominalTutorial

open Nominal.Core Nominal.Set LambdaCalculus LambdaCalculus.Term

universe u
variable {α : Type u} [Name α]

/-! ## Atoms, support, and fresh selection -/

theorem supportOfOpenAbstraction (a x : α) (hxa : x ≠ a) :
    supp (lam a (app (var a) (var x))) = {x} := by
  ext b
  simp only [supp_term_lam, supp_term_app, supp_term_var, Finset.mem_sdiff,
    Finset.mem_union, Finset.mem_singleton]
  aesop

/-- The chosen atom avoids both an arbitrary term and an external parameter.
The generated hypotheses are consumed, including the named product split. -/
theorem freshForTermAndAtom (t : Term α) (x : α) :
    ∃ a : α, a # t ∧ a ≠ x := by
  choose_fresh a from (t, x) with hf
  split_fresh hf1 with hat hax
  exact ⟨a, hat, (fresh_atoms a x).mp hax⟩

/-! ## Alpha equality and nested binders -/

theorem alphaIdentity (a b : α) : lam a (var a) = lam b (var b) := by
  rw [lam_eq_swap (b := b) (by simp)]
  simp

/-- Repeated displayed binders are allowed. Equality respects their scopes;
there is no global requirement that all binder names be distinct. -/
theorem nestedAlpha (a b c : α) :
    lam a (lam a (var a)) = lam b (lam c (var c)) := by
  rw [lam_eq_swap (b := b)
    (fresh_term_lam_of_fresh b a _ (by simp))]
  simp only [smul_lam, smul_var]
  exact congrArg (lam b) (alphaIdentity _ c)

/-! ## Supported functions as ordinary clients -/

def variableHandler : NFun α α (Term α) :=
  NFun.equivariant var (fun π a => (smul_var π a).symm)

def application : NFun α (Term α × Term α) (Term α) :=
  NFun.equivariant (fun p => app p.1 p.2) (by intro π p; simp)

def abstraction : NFun α (α × Term α) (Term α) :=
  NFun.equivariant (fun p => lam p.1 p.2) (by intro π p; simp)

/-- A named finite-support certificate keeps the witness in `Prop` and lets
application simplification match the smart constructor's typed proof argument. -/
theorem replaceVariableSupported (x : α) (s : Term α) :
    FinSupported (PFun.mk (α := α) (fun a => if a = x then s else var a)) :=
  ⟨{x} ∪ supp s, by supports_nfun from x s⟩

/-- An explicit capture bound with a kernel-checked support proof. The function
body is computable; the noncomputable `supp s` stays inside the proof field. -/
def replaceVariable (x : α) (s : Term α) : NFun α α (Term α) :=
  NFun.ofFun (fun a => if a = x then s else var a)
    (replaceVariableSupported x s)

theorem replaceVariableAt (x : α) (s : Term α) : replaceVariable x s x = s := by
  simp [replaceVariable]

/-- Fixing the left child of application is partial application of a curry. -/
theorem partialApplication (t s : Term α) : application.curry t s = app t s := rfl

theorem curryRoundTrip : (application (α := α)).curry.uncurry = application := by
  simp

theorem partialSupport (t : Term α) : supp (application.curry t) ⊆ supp t := by
  simpa [application] using NFun.supp_curry_apply_le application t

theorem composeAndMap (t : Term α) (xs : List α) :
    xs.map ((application.curry t).comp variableHandler) = xs.map (fun a => app t (var a)) := by
  simp [application, variableHandler]

theorem rewriteUnderFunction (f g : NFun α (Term α) (Term α)) (h : f = g)
    (ts : List (Term α)) : ts.map f = ts.map g := by
  rw [h]

/-- Substitution is jointly equivariant in the variable, replacement, and term.
After fixing the first two parameters the result is finitely supported. -/
theorem substitutionJoint :
    IsEquivariant₂ α (fun (p : α × Term α) (t : Term α) => t[p.1 := p.2]) :=
  ⟨fun π p t => (subst_equivariant π t p.1 p.2).symm⟩

noncomputable def substitute (x : α) (s : Term α) : NFun α (Term α) (Term α) :=
  NFun.fromParam (fun (p : α × Term α) (t : Term α) => t[p.1 := p.2])
    substitutionJoint (x, s)

@[simp] theorem substituteApply (x : α) (s t : Term α) :
    substitute x s t = t[x := s] := by simp [substitute]

theorem substituteSupport (x : α) (s : Term α) :
    supp (substitute x s) ⊆ {x} ∪ supp s := by
  simpa [substitute, supp_prod, supp_atom] using
    NFun.supp_fromParam_le
      (fun (p : α × Term α) (t : Term α) => t[p.1 := p.2]) substitutionJoint (x, s)

/-! ## Iteration and strong term induction -/

/-- The abstraction handler removes its binder from the output support. This
is the FCB condition; equivariance of a handler alone would not imply it. -/
theorem abstractionFCB (A : Finset α) :
    ∀ a y, a # A → a # (abstraction : NFun α (α × Term α) (Term α)) (a, y) :=
  NFun.fcb_of_binder abstraction (fun a y => fresh_term_lam_of_eq a y) A

noncomputable def rebuild : NFun α (Term α) (Term α) :=
  recNoContextNFun variableHandler application abstraction ∅
    (by simp [variableHandler]) (by simp [application]) (by simp [abstraction])
    (abstractionFCB ∅)

@[simp] theorem rebuildVariable (a : α) : rebuild (var a) = var a := by
  simp [rebuild, variableHandler]

@[simp] theorem rebuildApplication (t s : Term α) :
    rebuild (app t s) = app (rebuild t) (rebuild s) := by
  simp [rebuild, application]

theorem rebuildAbstraction (a : α) (t : Term α) :
    rebuild (lam a t) = lam a (rebuild t) := by
  simp only [rebuild, recNoContextNFun_apply]
  rw [recNoContext_lam _ _ _ _ _ _ _ _ a t (by simp)]
  rfl

theorem rebuildSupport : supp (rebuild (α := α)) = ∅ :=
  Finset.subset_empty.mp (supp_recNoContextNFun_le ..)

/-- The public uniqueness contract accepts an ordinary candidate function,
even when its lambda equation needs its own finite avoidance set. -/
theorem rebuildUnique (g : Term α → Term α) (B : Finset α)
    (hv : ∀ a, g (var a) = var a)
    (ha : ∀ t s, g (app t s) = app (g t) (g s))
    (hl : ∀ a t, a # B → g (lam a t) = lam a (g t)) :
    (rebuild : Term α → Term α) = g :=
  recNoContext_unique variableHandler application abstraction ∅
    (by simp [variableHandler]) (by simp [application]) (by simp [abstraction])
    (abstractionFCB ∅) g B hv ha hl

/-- This induction is on a term. It needs no reduction derivation. The finite
avoidance set is empty because all three reconstruction handlers are equivariant. -/
theorem rebuildIdentity (t : Term α) : rebuild t = t := by
  induction t using strong_ind_finset (∅ : Finset α) with
  | hVar a => exact rebuildVariable a
  | hApp t s iht ihs => simp [iht, ihs]
  | hLam a t _ ih => rw [rebuildAbstraction, ih]

/-! ## Capture avoidance and substitution composition -/

/-- In `(λy. x)[x := y]`, keeping `y` as binder would capture the replacement.
Choose a new binder and expose only the public renaming/computation equations. -/
theorem renameToAvoidCapture (x y : α) (hxy : x ≠ y) :
    ∃ z : α, z ≠ x ∧ z ≠ y ∧
      (lam y (var x))[x := var y] = lam z (var y) ∧ ¬ y # lam z (var y) := by
  choose_fresh z from x y
  have hzx : z ≠ x := (fresh_atoms z x).mp zFresh1
  have hzy : z ≠ y := (fresh_atoms z y).mp zFresh2
  refine ⟨z, hzx, hzy, ?_, ?_⟩
  · rw [subst_lam_rename y z (var x) x (var y) (by simpa using hzx)]
    have hz : z # (x, var y) := by simp [hzx, hzy]
    rw [subst_lam _ _ _ _ hz]
    simp [hxy, hzx.symm]
  · simp [hzy.symm]

/-- Composition at the supported-function level. Both hypotheses of the
substitution lemma are retained; in general the substitutions do not commute. -/
theorem substitutionComposition (x y : α) (s r : Term α)
    (hxy : x ≠ y) (hxr : x # r) :
    (substitute y r).comp (substitute x s) =
      (substitute x (s[y := r])).comp (substitute y r) := by
  ext t
  simpa using subst_subst x y t s r hxy hxr

/-! ## Fresh induction on a derivation -/

/-- Here induction is on `h : t ⇉ t'`, with atom `x` as the avoidance context.
The arbitrary predicate `q` is captured by the motive: it needs no action or
finite support. Freshness of each rule binder removes the bound-atom alternative. -/
theorem parallelPreservesFreshWhen (q : α → Prop) {t t' : Term α}
    (h : t ⇉ t') (x : α) (hq : q x) (hx : x # t) : x # t' := by
  apply Parallel.strong_ind (P := fun t t' x => q x → x # t → x # t')
    (hVar := fun _ _ _ hx => hx)
    (hApp := fun _ _ _ _ x _ _ iht ihs hq hx => by
      obtain ⟨ht, hs⟩ := (fresh_term_app _ _ _).mp hx
      exact (fresh_term_app _ _ _).mpr ⟨iht x hq ht, ihs x hq hs⟩)
    (hLam := fun a t _ x _ ha ih hq hx => by
      have hxa : x ≠ a := ((fresh_atoms a x).mp ha).symm
      have hxt := ((fresh_term_lam x a t).mp hx).resolve_left hxa
      exact fresh_term_lam_of_fresh _ _ _ (ih x hq hxt))
    (hBeta := fun a t _ s _ x _ _ ha _ _ iht ihs hq hx => by
      obtain ⟨hxt, hxs⟩ := (fresh_term_app _ _ _).mp hx
      have hxa : x ≠ a := ((fresh_atoms a x).mp ha).symm
      have hxt := ((fresh_term_lam x a t).mp hxt).resolve_left hxa
      exact subst_fresh_of_fresh _ _ _ _ (iht x hq hxt) (ihs x hq hxs))
    h x hq hx

/-! ## From parallel reduction to Church–Rosser -/

abbrev identityRedex (a : α) (t : Term α) : Term α := app (lam a (var a)) t

theorem contractIdentity (a : α) (t : Term α) : identityRedex a t →β t := by
  simpa [identityRedex] using Beta.beta a (var a) t

/-- Both inputs to parallel substitution take genuine reduction steps. -/
theorem substituteRelatedInputs (a b x y : α) :
    (identityRedex a (var x))[x := identityRedex b (var y)] ⇉ var y := by
  simpa using (contractIdentity a (var x)).to_parallel.subst
    (contractIdentity b (var y)).to_parallel x

/-- A beta peak: the outer contraction duplicates the reducible argument,
whereas the other branch reduces that argument first. Parallel diamond joins
these distinct immediate reducts without a freshness assumption on the atoms. -/
theorem diamondForDuplication (a b x : α) :
    ∃ p, app (identityRedex b (var x)) (identityRedex b (var x)) ⇉ p ∧
      app (lam a (app (var a) (var a))) (var x) ⇉ p := by
  have outer : app (lam a (app (var a) (var a))) (identityRedex b (var x)) →β
      app (identityRedex b (var x)) (identityRedex b (var x)) := by
    simpa using Beta.beta a (app (var a) (var a)) (identityRedex b (var x))
  have argument := Beta.app_right (lam a (app (var a) (var a)))
    (contractIdentity b (var x))
  exact outer.to_parallel.diamond argument.to_parallel

theorem closureCorrespondence {t s : Term α} :
    (t →β* s) ↔ Relation.ReflTransGen Parallel t s := betaStar_iff_parallelStar

/-- The common reduct of the displayed peak is the open term `x x`. -/
theorem duplicationSequence (a b x : α) :
    app (lam a (app (var a) (var a))) (identityRedex b (var x)) →β*
      app (var x) (var x) := by
  have step : app (lam a (app (var a) (var a))) (identityRedex b (var x)) ⇉
      app (var x) (var x) := by
    simpa using Parallel.beta a (Parallel.refl (app (var a) (var a)))
      (contractIdentity b (var x)).to_parallel
  exact step.to_betaStar

theorem joinConvertible {t s : Term α} (h : t ≡β s) :
    ∃ p, t →β* p ∧ s →β* p := h.church_rosser

/-- This also exercises confluence for an arbitrary competing finite sequence. -/
theorem joinDuplicationReduct (a b x : α) {s : Term α}
    (h : app (lam a (app (var a) (var a))) (identityRedex b (var x)) →β* s) :
    ∃ p, s →β* p ∧ app (var x) (var x) →β* p :=
  h.confluent (duplicationSequence a b x)

theorem variableApplicationNormal (x y : α) : BetaNormal (app (var x) (var y)) := by
  intro t h
  rcases Beta.app_iff.mp h with ⟨_, h, _⟩ | ⟨_, h, _⟩ | ⟨_, _, heq, _⟩
  · exact Beta.not_var h
  · exact Beta.not_var h
  · exact var_ne_lam _ _ _ heq

/-- Normality and convertibility are hypotheses. Nothing here supplies a
normalization algorithm or claims that every untyped term has a normal form. -/
theorem uniqueNormalResult (a b x : α) {n : Term α}
    (h : app (lam a (app (var a) (var a))) (identityRedex b (var x)) ≡β n)
    (hn : BetaNormal n) : n = app (var x) (var x) := by
  have conversion := h.symm.trans (BetaEq.of_betaStar (duplicationSequence a b x))
  exact conversion.normal_unique hn (variableApplicationNormal x x)

end NominalTutorial

-- Compiling this client also checks every tutorial declaration for admissions
-- or additional axioms. The standard classical Lean foundations are accepted.
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "NominalTutorial." then
      let axioms ← collectAxioms name
      let extra := axioms.filter fun a =>
        a != `propext && a != `Classical.choice && a != `Quot.sound
      unless extra.isEmpty do
        throwError "{name}: unexpected axioms {extra}"
