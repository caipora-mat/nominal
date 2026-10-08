/-
Copyright (c) 2026 Nominal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nominal contributors
-/
import Package.Foundations.PredicateDescent
import Package.Foundations.SupportedPredicateLogic
import Mathlib.GroupTheory.GroupAction.SubMulAction

/-!
# Supported pullback and quotient predicates

Equivariant pullback retains every predicate bound, reflecting it for surjections.
Compatible supported predicates form a restricted action via SubMulAction. The
quotient correspondence selects both that action and the canonical quotient
action explicitly; it never asks instance search to guess relation invariance.
Neither source nor quotient needs carrier-wide nominality. Exact sufficient
bounds yield least-support and individual-context freshness agreement over
infinite atoms. Logical preservation uses the existing Boolean structure.
-/

namespace NominalPackage
universe u v w

namespace SupportedPred
variable {A : Type u} {X : Type v} {Y : Type w}
variable [MulAction (Perm A) X] [MulAction (Perm A) Y]

/-- Precompose with an equivariant ordinary map, retaining predicate support. -/
def pullback (P : SupportedPred A Y) (q : X → Y) (hq : Equivariant A q) : SupportedPred A X :=
  ofFun A (P ∘ q) (P.supported.pullback hq)

@[simp] theorem pullback_apply (P : SupportedPred A Y) (q : X → Y)
    (hq : Equivariant A q) (x : X) : P.pullback q hq x ↔ P (q x) := Iff.rfl
@[simp] theorem coe_pullback (P : SupportedPred A Y) (q : X → Y) (hq : Equivariant A q) :
    (P.pullback q hq : X → Prop) = P ∘ q := rfl

theorem pullback_smul (q : X → Y) (hq : Equivariant A q) (π : Perm A) (P : SupportedPred A Y) :
    (π • P).pullback q hq = π • P.pullback q hq :=
  DFunLike.coe_injective (renamePred_pullback q hq π P)

theorem supports_pullback {S : Finset A} {P : SupportedPred A Y} {q : X → Y}
    (hP : Supports S P) (hq : Equivariant A q) : Supports S (P.pullback q hq) :=
  (supports_iff _ _).2 (((supports_iff _ _).1 hP).pullback hq)

theorem supports_pullback_iff (q : X → Y) (hq : Equivariant A q)
    (hsurj : Function.Surjective q) (S : Finset A) (P : SupportedPred A Y) :
    Supports S (P.pullback q hq) ↔ Supports S P :=
  (supports_iff _ _).trans ((supportsPred_pullback_iff q hq hsurj S P).trans (supports_iff _ _).symm)

theorem support_pullback [Infinite A] (P : SupportedPred A Y) (q : X → Y)
    (hq : Equivariant A q) (hsurj : Function.Surjective q) :
    support A (P.pullback q hq) = support A P :=
  le_antisymm
    (support_minimal A ((supports_pullback_iff q hq hsurj _ P).2 (supports_support A P)))
    (support_minimal A ((supports_pullback_iff q hq hsurj _ P).1 (supports_support A _)))

@[simp] theorem pullback_top (q : X → Y) (hq : Equivariant A q) :
    (⊤ : SupportedPred A Y).pullback q hq = ⊤ := by ext x; rfl
@[simp] theorem pullback_bot (q : X → Y) (hq : Equivariant A q) :
    (⊥ : SupportedPred A Y).pullback q hq = ⊥ := by ext x; rfl

theorem pullback_compl (q : X → Y) (hq : Equivariant A q) (P : SupportedPred A Y) :
    Pᶜ.pullback q hq = (P.pullback q hq)ᶜ := by ext x; rfl
theorem pullback_inf (q : X → Y) (hq : Equivariant A q) (P Q : SupportedPred A Y) :
    (P ⊓ Q).pullback q hq = P.pullback q hq ⊓ Q.pullback q hq := by ext x; rfl
theorem pullback_sup (q : X → Y) (hq : Equivariant A q) (P Q : SupportedPred A Y) :
    (P ⊔ Q).pullback q hq = P.pullback q hq ⊔ Q.pullback q hq := by ext x; rfl
theorem pullback_himp (q : X → Y) (hq : Equivariant A q) (P Q : SupportedPred A Y) :
    (P ⇨ Q).pullback q hq = P.pullback q hq ⇨ Q.pullback q hq := by ext x; rfl
theorem pullback_biimp (q : X → Y) (hq : Equivariant A q) (P Q : SupportedPred A Y) :
    (P.biimp Q).pullback q hq = (P.pullback q hq).biimp (Q.pullback q hq) := by ext x; rfl
end SupportedPred

namespace PredicateDescent
variable (A : Type u) {X : Type v} [MulAction (Perm A) X]

/-- Supported predicates that are constant, up to Iff, on each equivalence class. -/
abbrev CompatiblePred (s : Setoid X) :=
  {p : SupportedPred A X // Compatible s (fun x => p x)}

private def compatibleSubMulAction (s : Setoid X) (hs : SMulInvariant (Perm A) s) :
    SubMulAction (Perm A) (SupportedPred A X) where
  carrier := {p | Compatible s (fun x => p x)}
  smul_mem' π _ hp := compatible_rename s hs _ hp π

/-- Restrict the existing predicate action using the supplied relation invariance. -/
abbrev compatibleAction (s : Setoid X) (hs : SMulInvariant (Perm A) s) :
    MulAction (Perm A) (CompatiblePred A s) :=
  (compatibleSubMulAction A s hs).mulAction

@[simp] theorem compatible_val_smul (s : Setoid X) (hs : SMulInvariant (Perm A) s) :
    letI := compatibleAction A s hs
    ∀ (π : Perm A) (p : CompatiblePred A s), (π • p).val = π • p.val := by
  let _ := compatibleAction A s hs
  intro π p
  rfl

/-- Restriction preserves exactly the sufficient bounds of the underlying predicate. -/
theorem supports_compatible_iff (s : Setoid X) (hs : SMulInvariant (Perm A) s) (S : Finset A) :
    letI := compatibleAction A s hs
    ∀ p : CompatiblePred A s, Supports S p ↔ Supports S p.val := by
  let _ := compatibleAction A s hs
  intro p
  exact (ActionSupport.supports_map_iff Subtype.val (compatible_val_smul A s hs)
    Subtype.val_injective (S : Set A) p).symm

/-- Nominality of the restricted action, supplied explicitly rather than guessed. -/
theorem compatibleNominal (s : Setoid X) (hs : SMulInvariant (Perm A) s) :
    letI := compatibleAction A s hs
    Nominal A (CompatiblePred A s) := by
  let _ := compatibleAction A s hs
  refine ⟨fun p => ?_⟩
  obtain ⟨S, hS⟩ := Nominal.finitelySupported (A := A) p.val
  exact ⟨S, (supports_compatible_iff A s hs S p).2 hS⟩

/-- Ordinary descent with the induced finite-support certificate in a proof field. -/
def descendSupported (s : Setoid X) (hs : SMulInvariant (Perm A) s)
    (p : SupportedPred A X) (hp : Compatible s (fun x => p x)) :
    letI := QuotientAction.mulAction s hs
    SupportedPred A (Quotient s) :=
  letI := QuotientAction.mulAction s hs
  SupportedPred.ofFun A (descend s p hp) ((finitelySupported_descend_iff s hs p hp).2 p.supported)

@[simp] theorem descendSupported_mk (s : Setoid X) (hs : SMulInvariant (Perm A) s)
    (p : SupportedPred A X) (hp : Compatible s (fun x => p x)) (x : X) :
    letI := QuotientAction.mulAction s hs
    descendSupported A s hs p hp (Quotient.mk s x) ↔ p x := Iff.rfl

theorem supports_descendSupported_iff (s : Setoid X) (hs : SMulInvariant (Perm A) s)
    (S : Finset A) (p : SupportedPred A X) (hp : Compatible s (fun x => p x)) :
    letI := QuotientAction.mulAction s hs
    Supports S (descendSupported A s hs p hp) ↔ Supports S p := by
  let _ := QuotientAction.mulAction s hs
  exact (SupportedPred.supports_iff _ _).trans
    ((supports_descend_iff s hs S p hp).trans (SupportedPred.supports_iff _ _).symm)

/-- Supported quotient predicates correspond to compatible supported predicates. -/
def supportedEquiv (s : Setoid X) (hs : SMulInvariant (Perm A) s) :
    letI := QuotientAction.mulAction s hs
    SupportedPred A (Quotient s) ≃ CompatiblePred A s := by
  letI := QuotientAction.mulAction s hs
  exact {
    toFun P := ⟨P.pullback (Quotient.mk s) (QuotientAction.equivariant_mk A s hs),
      compatible_pullback s P⟩
    invFun p := descendSupported A s hs p.val p.property
    left_inv P := DFunLike.coe_injective (descend_pullback s P)
    right_inv p := Subtype.ext (SupportedPred.ext fun _ => Iff.rfl) }

@[simp] theorem supportedEquiv_apply (s : Setoid X) (hs : SMulInvariant (Perm A) s) :
    letI := QuotientAction.mulAction s hs
    ∀ (P : SupportedPred A (Quotient s)) (x : X),
      (supportedEquiv A s hs P).val x ↔ P (Quotient.mk s x) := by
  let _ := QuotientAction.mulAction s hs
  intro P x
  rfl

@[simp] theorem supportedEquiv_symm_apply (s : Setoid X) (hs : SMulInvariant (Perm A) s)
    (p : CompatiblePred A s) (x : X) :
    letI := QuotientAction.mulAction s hs
    (supportedEquiv A s hs).symm p (Quotient.mk s x) ↔ p.val x := Iff.rfl

@[simp] theorem supportedEquiv_symm_apply_apply (s : Setoid X) (hs : SMulInvariant (Perm A) s) :
    letI := QuotientAction.mulAction s hs
    ∀ P : SupportedPred A (Quotient s),
      (supportedEquiv A s hs).symm (supportedEquiv A s hs P) = P :=
  (supportedEquiv A s hs).symm_apply_apply

@[simp] theorem supportedEquiv_apply_symm_apply (s : Setoid X) (hs : SMulInvariant (Perm A) s)
    (p : CompatiblePred A s) :
    letI := QuotientAction.mulAction s hs
    supportedEquiv A s hs ((supportedEquiv A s hs).symm p) = p :=
  (supportedEquiv A s hs).apply_symm_apply p

theorem supportedEquiv_smul (s : Setoid X) (hs : SMulInvariant (Perm A) s) :
    letI := QuotientAction.mulAction s hs
    letI := compatibleAction A s hs
    ∀ (π : Perm A) (P : SupportedPred A (Quotient s)),
      supportedEquiv A s hs (π • P) = π • supportedEquiv A s hs P := by
  let _ := QuotientAction.mulAction s hs
  let _ := compatibleAction A s hs
  intro π P
  exact Subtype.ext (SupportedPred.pullback_smul _ (QuotientAction.equivariant_mk A s hs) π P)

theorem supportedEquiv_symm_smul (s : Setoid X) (hs : SMulInvariant (Perm A) s) :
    letI := QuotientAction.mulAction s hs
    letI := compatibleAction A s hs
    ∀ (π : Perm A) (p : CompatiblePred A s),
      (supportedEquiv A s hs).symm (π • p) = π • (supportedEquiv A s hs).symm p := by
  let _ := QuotientAction.mulAction s hs
  let _ := compatibleAction A s hs
  intro π p
  apply (supportedEquiv A s hs).injective
  rw [supportedEquiv_smul, supportedEquiv_apply_symm_apply, supportedEquiv_apply_symm_apply]

/-- Every supplied bound is preserved and reflected, independently of least support. -/
theorem supports_supportedEquiv_iff (s : Setoid X) (hs : SMulInvariant (Perm A) s) (S : Finset A) :
    letI := QuotientAction.mulAction s hs
    letI := compatibleAction A s hs
    ∀ P : SupportedPred A (Quotient s), Supports S (supportedEquiv A s hs P) ↔ Supports S P := by
  let _ := QuotientAction.mulAction s hs
  let _ := compatibleAction A s hs
  intro P
  exact ActionSupport.supports_map_iff (supportedEquiv A s hs) (supportedEquiv_smul A s hs)
    (supportedEquiv A s hs).injective (S : Set A) P

theorem support_supportedEquiv [Infinite A] (s : Setoid X) (hs : SMulInvariant (Perm A) s) :
    letI := QuotientAction.mulAction s hs
    letI := compatibleAction A s hs
    letI := compatibleNominal A s hs
    ∀ P : SupportedPred A (Quotient s), support A (supportedEquiv A s hs P) = support A P := by
  let _ := QuotientAction.mulAction s hs
  let _ := compatibleAction A s hs
  let _ := compatibleNominal A s hs
  intro P
  exact le_antisymm
    (support_minimal A ((supports_supportedEquiv_iff A s hs _ P).2 (supports_support A P)))
    (support_minimal A ((supports_supportedEquiv_iff A s hs _ P).1 (supports_support A _)))

/-- Freshness agreement uses only the individual context certificate, not a nominal carrier. -/
theorem freshWith_supportedEquiv_iff [Infinite A] (s : Setoid X) (hs : SMulInvariant (Perm A) s) :
    letI := QuotientAction.mulAction s hs
    letI := compatibleAction A s hs
    letI := compatibleNominal A s hs
    ∀ (P : SupportedPred A (Quotient s)) {C : Type w} [MulAction (Perm A) C]
      {c : C} (hc : FinitelySupported A c),
      (Nominal.finitelySupported (A := A) P).FreshWith hc ↔
        (Nominal.finitelySupported (A := A) (supportedEquiv A s hs P)).FreshWith hc := by
  let _ := QuotientAction.mulAction s hs
  let _ := compatibleAction A s hs
  let _ := compatibleNominal A s hs
  intro P C _ c hc
  change Disjoint (support A P) hc.support ↔ Disjoint (support A (supportedEquiv A s hs P)) hc.support
  rw [support_supportedEquiv]

/- Logical preservation is inherited pointwise; the compatible subtype needs no new algebra. -/

@[simp] theorem descendSupported_top (s : Setoid X) (hs : SMulInvariant (Perm A) s) :
    letI := QuotientAction.mulAction s hs
    descendSupported A s hs ⊤ (Compatible.const s True) = ⊤ := by
  let _ := QuotientAction.mulAction s hs
  ext c
  induction c using Quotient.inductionOn with
  | h x => rfl

@[simp] theorem descendSupported_bot (s : Setoid X) (hs : SMulInvariant (Perm A) s) :
    letI := QuotientAction.mulAction s hs
    descendSupported A s hs ⊥ (Compatible.const s False) = ⊥ := by
  let _ := QuotientAction.mulAction s hs
  ext c
  induction c using Quotient.inductionOn with
  | h x => rfl

theorem descendSupported_compl (s : Setoid X) (hs : SMulInvariant (Perm A) s)
    (p : SupportedPred A X) (hp : Compatible s (fun x => p x)) :
    letI := QuotientAction.mulAction s hs
    descendSupported A s hs pᶜ hp.not = (descendSupported A s hs p hp)ᶜ := by
  let _ := QuotientAction.mulAction s hs
  ext c
  induction c using Quotient.inductionOn with
  | h x => rfl

theorem descendSupported_inf (s : Setoid X) (hs : SMulInvariant (Perm A) s)
    (p q : SupportedPred A X) (hp : Compatible s (fun x => p x)) (hq : Compatible s (fun x => q x)) :
    letI := QuotientAction.mulAction s hs
    descendSupported A s hs (p ⊓ q) (hp.and hq) =
      descendSupported A s hs p hp ⊓ descendSupported A s hs q hq := by
  let _ := QuotientAction.mulAction s hs
  ext c
  induction c using Quotient.inductionOn with
  | h x => rfl

theorem descendSupported_sup (s : Setoid X) (hs : SMulInvariant (Perm A) s)
    (p q : SupportedPred A X) (hp : Compatible s (fun x => p x)) (hq : Compatible s (fun x => q x)) :
    letI := QuotientAction.mulAction s hs
    descendSupported A s hs (p ⊔ q) (hp.or hq) =
      descendSupported A s hs p hp ⊔ descendSupported A s hs q hq := by
  let _ := QuotientAction.mulAction s hs
  ext c
  induction c using Quotient.inductionOn with
  | h x => rfl

theorem descendSupported_himp (s : Setoid X) (hs : SMulInvariant (Perm A) s)
    (p q : SupportedPred A X) (hp : Compatible s (fun x => p x)) (hq : Compatible s (fun x => q x)) :
    letI := QuotientAction.mulAction s hs
    descendSupported A s hs (p ⇨ q) (hp.imp hq) =
      descendSupported A s hs p hp ⇨ descendSupported A s hs q hq := by
  let _ := QuotientAction.mulAction s hs
  ext c
  induction c using Quotient.inductionOn with
  | h x => rfl

theorem descendSupported_biimp (s : Setoid X) (hs : SMulInvariant (Perm A) s)
    (p q : SupportedPred A X) (hp : Compatible s (fun x => p x)) (hq : Compatible s (fun x => q x)) :
    letI := QuotientAction.mulAction s hs
    descendSupported A s hs (p.biimp q) ((hp.imp hq).and (hq.imp hp)) =
      (descendSupported A s hs p hp).biimp (descendSupported A s hs q hq) := by
  let _ := QuotientAction.mulAction s hs
  ext c
  induction c using Quotient.inductionOn with
  | h x => rfl

end PredicateDescent
end NominalPackage
