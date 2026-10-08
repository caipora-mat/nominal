/-
Copyright (c) 2026 Nominal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nominal contributors
-/
import Package.Foundations.FreshQuantifier
import Package.Foundations.SupportedPredicateLogic

/-!
# Fresh projection of supported predicates

Fresh projection uses the ordinary cofinite operator and preserves the joint
relation's bound, without infinitude or nominality of its parameter carrier.
Least-support and atom-freshness conveniences add infinitude and reuse the
existing support-disjointness relation.
-/

namespace NominalPackage.SupportedPred
universe u v
variable {A : Type u} {X : Type v} [MulAction (Perm A) X]

/-- Cofinitely quantify the atom input of a jointly supported relation. -/
def fresh (R : SupportedPred A (X × A)) : SupportedPred A X :=
  ofFun A (fun x => Freshly (fun a => R (x,a))) R.supported.fresh

@[simp] theorem fresh_apply (R : SupportedPred A (X × A)) (x : X) :
    R.fresh x ↔ Freshly (fun a => R (x,a)) := Iff.rfl

@[simp] theorem coe_fresh (R : SupportedPred A (X × A)) :
    (R.fresh : X → Prop) = (fun x => Freshly (fun a => R (x,a))) := rfl

theorem fresh_smul (π : Perm A) (R : SupportedPred A (X × A)) :
    (π • R).fresh = π • R.fresh := by
  ext x
  change Freshly (fun a => R (π⁻¹ • x, π⁻¹ • a)) ↔ Freshly (fun a => R (π⁻¹ • x, a))
  exact Freshly.reindex (π⁻¹).toEquiv (fun a => R (π⁻¹ • x, a))

theorem supports_fresh {S : Finset A} {R : SupportedPred A (X × A)} (hR : Supports S R) :
    Supports S R.fresh :=
  (supports_iff _ _).2 ((supports_iff _ _).1 hR).fresh

theorem support_fresh_subset [Infinite A] (R : SupportedPred A (X × A)) :
    support A R.fresh ⊆ support A R :=
  support_minimal A (supports_fresh (supports_support A R))

/-- Evaluate a supported atom predicate at an atom fresh for the predicate value. -/
theorem freshly_iff_of_fresh [Infinite A] (p : SupportedPred A A) {a : A}
    (ha : Fresh A a p) : Freshly (fun b => p b) ↔ p a :=
  ((supports_iff _ _).1 (supports_support A p)).freshly_iff
    ((fresh_iff_notMem_support A a p).1 ha)

end NominalPackage.SupportedPred
