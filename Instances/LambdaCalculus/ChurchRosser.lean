import Instances.LambdaCalculus.ParallelDiamond
import Instances.LambdaCalculus.ReductionClosure

/-!
# Beta confluence, Church–Rosser, and uniqueness of normal forms

Every beta step is parallel, and every parallel step is a finite beta sequence.
Their reflexive-transitive closures therefore coincide. The parallel diamond
theorem and Mathlib's `Relation.church_rosser` give confluence of this closure.
Confluence makes joinability an equivalence relation, so `Term.BetaEq` (the
existing `Relation.EqvGen Term.Beta`) is exactly common-reduct joinability.

All statements concern arbitrary open quotient terms and full contextual beta
reduction, including beneath lambdas. Normality means no outgoing beta step;
normal forms are unique when they exist. Neither termination nor existence of
normal forms is asserted or assumed.

The bridge reuses `BetaStar.app` and `BetaStar.lam`; the general closure facts
are Mathlib's `ReflTransGen.mono`, `reflTransGen_closed`, `church_rosser`,
`equivalence_join`, `EqvGen.mono`, `Equivalence.eqvGen_iff`, and
`reflTransGen_iff_eq`. No new closure relation or binder machinery is needed.
-/

namespace LambdaCalculus

open Nominal.Core Nominal.Set

universe u
variable {α : Type u} [Name α]

namespace Term

/-- Every contextual beta step is a parallel step. -/
theorem Beta.to_parallel {t s : Term α} (h : t →β s) : t ⇉ s := by
  induction h with
  | beta a t s => exact Parallel.beta a (Parallel.refl t) (Parallel.refl s)
  | app_left _ s ih => exact Parallel.app ih (Parallel.refl s)
  | app_right t _ ih => exact Parallel.app (Parallel.refl t) ih
  | lam a _ ih => exact Parallel.lam a ih

/-- Sequentialize a parallel step. For contraction, first reduce the body and
argument in their contexts, then contract the resulting redex. -/
theorem Parallel.to_betaStar {t s : Term α} (h : t ⇉ s) : t →β* s := by
  induction h with
  | var a => exact BetaStar.refl (Term.var a)
  | app _ _ iht ihs => exact BetaStar.app iht ihs
  | lam a _ ih => exact BetaStar.lam a ih
  | beta a _ _ iht ihs =>
    exact (BetaStar.app (BetaStar.lam a iht) ihs).trans
      (BetaStar.single (Beta.beta a _ _))

/-- Beta and parallel reduction generate the same finite directed sequences. -/
theorem betaStar_iff_parallelStar {t s : Term α} :
    (t →β* s) ↔ Relation.ReflTransGen Parallel t s :=
  ⟨Relation.ReflTransGen.mono (fun _ _ h ↦ h.to_parallel) _ _,
    Relation.reflTransGen_closed (fun _ _ h ↦ h.to_betaStar) _ _⟩

/-- Relation equality form of `betaStar_iff_parallelStar`. -/
theorem betaStar_eq_parallelStar :
    (BetaStar : Term α → Term α → Prop) = Relation.ReflTransGen Parallel :=
  funext fun _ ↦ funext fun _ ↦ propext betaStar_iff_parallelStar

/-- Parallel diamond implies confluence of its reflexive-transitive closure.
This is a direct instance of Mathlib's general relation theorem. -/
theorem Parallel.confluent {t t₁ t₂ : Term α}
    (h₁ : Relation.ReflTransGen Parallel t t₁)
    (h₂ : Relation.ReflTransGen Parallel t t₂) :
    Relation.Join (Relation.ReflTransGen Parallel) t₁ t₂ := by
  apply Relation.church_rosser (r := Parallel) ?_ h₁ h₂
  intro _ _ _ h₁ h₂
  obtain ⟨p, h₁p, h₂p⟩ := h₁.diamond h₂
  exact ⟨p, Relation.ReflGen.single h₁p, Relation.ReflTransGen.single h₂p⟩

/-- Confluence of full beta reduction on arbitrary open quotient terms.
The premises and both joining edges are finite beta sequences. -/
theorem BetaStar.confluent {t t₁ t₂ : Term α} (h₁ : t →β* t₁) (h₂ : t →β* t₂) :
    ∃ p, t₁ →β* p ∧ t₂ →β* p := by
  obtain ⟨p, h₁p, h₂p⟩ := Parallel.confluent
    (betaStar_iff_parallelStar.mp h₁) (betaStar_iff_parallelStar.mp h₂)
  exact ⟨p, betaStar_iff_parallelStar.mpr h₁p, betaStar_iff_parallelStar.mpr h₂p⟩

/-- Church–Rosser: beta-convertible terms have a common beta reduct.
Unlike `BetaStar.confluent`, the premise allows steps in either direction. -/
theorem BetaEq.church_rosser {t s : Term α} (h : t ≡β s) :
    ∃ p, t →β* p ∧ s →β* p := by
  have hj : Equivalence (Relation.Join (BetaStar : Term α → Term α → Prop)) :=
    Relation.equivalence_join (fun _ _ _ ↦ BetaStar.confluent)
  exact hj.eqvGen_iff.mp (Relation.EqvGen.mono
    (fun _ s h ↦ ⟨s, BetaStar.single h, BetaStar.refl s⟩) _ _ h)

/-- Beta convertibility is exactly existence of a common beta reduct. -/
theorem BetaEq.iff_join {t s : Term α} :
    (t ≡β s) ↔ ∃ p, t →β* p ∧ s →β* p := by
  refine ⟨BetaEq.church_rosser, ?_⟩
  rintro ⟨p, htp, hsp⟩
  exact (BetaEq.of_betaStar htp).trans (BetaEq.of_betaStar hsp).symm

/-- A beta-normal term has no outgoing contextual beta step, even to itself. -/
def BetaNormal (t : Term α) : Prop := ∀ s, ¬ t →β s

/-- A finite beta sequence starting at a normal term ends at that same term. -/
theorem BetaNormal.eq_of_betaStar {t s : Term α} (ht : BetaNormal t)
    (h : t →β* s) : s = t :=
  (Relation.reflTransGen_iff_eq ht).mp h

/-- Two beta-normal reducts of a common source are equal as quotient terms. -/
theorem BetaStar.normal_unique {t t₁ t₂ : Term α}
    (h₁ : t →β* t₁) (h₂ : t →β* t₂) (hn₁ : BetaNormal t₁) (hn₂ : BetaNormal t₂) :
    t₁ = t₂ := by
  obtain ⟨p, h₁p, h₂p⟩ := h₁.confluent h₂
  exact (hn₁.eq_of_betaStar h₁p).symm.trans (hn₂.eq_of_betaStar h₂p)

/-- Beta-convertible normal forms are equal as quotient terms. -/
theorem BetaEq.normal_unique {t s : Term α} (h : t ≡β s)
    (ht : BetaNormal t) (hs : BetaNormal s) : t = s := by
  obtain ⟨p, htp, hsp⟩ := h.church_rosser
  exact (ht.eq_of_betaStar htp).symm.trans (hs.eq_of_betaStar hsp)

end Term

end LambdaCalculus
