import Nominal
import Instances.LambdaCalculus.Induction

/-! Research probes only, 2026-10-05. No library instances are installed. -/
open Nominal.Core Nominal.Set

namespace PredicateFoundations
universe u v w

section Descent
variable {X : Type u} (s : Setoid X)

def Compatible (P : X → Prop) : Prop := ∀ x y, s.r x y → (P x ↔ P y)

def descend (P : X → Prop) (h : Compatible s P) : Quotient s → Prop :=
  Quotient.lift P (fun x y hxy => propext (h x y hxy))

theorem descend_mk (P : X → Prop) (h : Compatible s P) (x : X) :
    descend s P h (Quotient.mk s x) = P x := rfl

def predicateEquiv : (Quotient s → Prop) ≃ {P : X → Prop // Compatible s P} where
  toFun Q := ⟨fun x => Q (Quotient.mk s x), fun x y h => by
    change Q (Quotient.mk s x) ↔ Q (Quotient.mk s y)
    rw [Quotient.sound h]⟩
  invFun P := descend s P.val P.property
  left_inv Q := by
    funext q
    induction q using Quotient.ind with
    | _ x => rfl
  right_inv P := by
    apply Subtype.ext
    rfl

-- Genuine dependence is supported when transport compatibility is supplied.
def dependentDescend {C : Quotient s → Sort v}
    (f : ∀ x, C (Quotient.mk s x))
    (h : ∀ x y (hxy : s.r x y), (Quotient.sound hxy) ▸ f x = f y) :
    ∀ q, C q := Quotient.rec f h

def dependentSingleton (q : Quotient s) : {r : Quotient s // r = q} :=
  Quotient.recOnSubsingleton q (fun x => ⟨Quotient.mk s x, rfl⟩)

-- Mutual maps between type-valued fibers are weaker than equality or equivalence.
example : (Unit → Bool) × (Bool → Unit) := ⟨fun _ => true, fun _ => ()⟩
theorem unit_ne_bool : Unit ≠ Bool := by
  intro h
  have : Subsingleton Bool := h ▸ inferInstanceAs (Subsingleton Unit)
  have htf : true = false := this.elim _ _
  cases htf

#print axioms predicateEquiv
#print axioms dependentDescend
#print axioms dependentSingleton
#print axioms unit_ne_bool
end Descent

@[instance_reducible] def propNominal {α : Type u} [Name α] : Nominal α Prop where
  smul _ P := P
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  finSupp _ := ⟨∅, fun _ _ => rfl⟩

section Predicates
variable {α : Type u} [Name α]
variable {X : Type v} [Nominal α X] {Y : Type w} [Nominal α Y]

def LogicalSupports (s : Finset α) (P : X → Prop) : Prop :=
  ∀ π : FinitePerm α, (∀ ⦃a⦄, a ∈ s → π a = a) → ∀ x, P (π • x) ↔ P x

theorem supports_iff_logical (s : Finset α) (P : X → Prop) :
    letI : Nominal α Prop := propNominal
    supports s (PFun.mk P : PFun α X Prop) ↔ LogicalSupports s P := by
  let : Nominal α Prop := propNominal
  rw [supports_pfun_iff]
  exact ⟨fun h π hπ x => Iff.of_eq (h π hπ x),
    fun h π hπ x => propext (h π hπ x)⟩

-- A subset presentation without a permutation instance on bare Set X.
abbrev SupportedSubset (α : Type u) [Name α] (X : Type v) [Nominal α X] :=
  {P : Set X // ∃ s : Finset α, LogicalSupports s P}

def supportedSubsetEquiv :
    letI : Nominal α Prop := propNominal
    NFun α X Prop ≃ SupportedSubset α X := by
  letI : Nominal α Prop := propNominal
  exact {
  toFun P := ⟨fun x => P x, by
    obtain ⟨s, hs⟩ := P.finSupp_toPFun
    exact ⟨s, (supports_iff_logical s P).mp hs⟩⟩
  invFun P := NFun.ofFun P.val (by
    obtain ⟨s, hs⟩ := P.property
    exact ⟨s, (supports_iff_logical s P.val).mpr hs⟩)
  left_inv P := by ext x; rfl
  right_inv P := by apply Subtype.ext; rfl }

theorem supports_not {s : Finset α} {P : X → Prop}
    (h : LogicalSupports s P) : LogicalSupports s (fun x => ¬ P x) := by
  intro π hπ x
  exact not_congr (h π hπ x)

theorem supports_and {s t : Finset α} {P Q : X → Prop}
    (hP : LogicalSupports s P) (hQ : LogicalSupports t Q) :
    LogicalSupports (s ∪ t) (fun x => P x ∧ Q x) := by
  intro π hπ x
  exact and_congr (hP π (fun a ha => hπ (Finset.mem_union_left t ha)) x)
    (hQ π (fun a ha => hπ (Finset.mem_union_right s ha)) x)

theorem supports_forall {s : Finset α} {R : X × Y → Prop}
    (hR : LogicalSupports s R) : LogicalSupports s (fun x => ∀ y, R (x, y)) := by
  intro π hπ x
  constructor
  · intro h y
    exact (hR π hπ (x, y)).mp (h (π • y))
  · intro h y
    have := (hR π hπ (x, π⁻¹ • y)).mpr (h (π⁻¹ • y))
    simpa using this

theorem supports_exists {s : Finset α} {R : X × Y → Prop}
    (hR : LogicalSupports s R) : LogicalSupports s (fun x => ∃ y, R (x, y)) := by
  intro π hπ x
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨π⁻¹ • y, (hR π hπ (x, π⁻¹ • y)).mp ?_⟩
    simpa using hy
  · rintro ⟨y, hy⟩
    exact ⟨π • y, (hR π hπ (x, y)).mpr hy⟩

theorem supportedSubset_image (π : FinitePerm α) :
    letI : Nominal α Prop := propNominal
    ∀ (P : NFun α X Prop) (x : X),
      (supportedSubsetEquiv (π • P)).val x ↔ ∃ y, P y ∧ π • y = x := by
  let : Nominal α Prop := propNominal
  intro P x
  change P (π⁻¹ • x) ↔ ∃ y, P y ∧ π • y = x
  constructor
  · intro h
    exact ⟨π⁻¹ • x, h, by simp⟩
  · rintro ⟨y, hy, rfl⟩
    simpa using hy

theorem infinite_coinfinite_unsupported (P : α → Prop)
    (hP : Set.Infinite {a | P a}) (hNotP : Set.Infinite {a | ¬ P a}) :
    letI : Nominal α Prop := propNominal
    ¬ FinSupported (PFun.mk P : PFun α α Prop) := by
  let : Nominal α Prop := propNominal
  rintro ⟨s, hs⟩
  obtain ⟨a, ha, has⟩ := hP.exists_notMem_finset s
  obtain ⟨b, hb, hbs⟩ := hNotP.exists_notMem_finset s
  have heq := (supports_iff_swap.mp hs) a b has hbs
  have hp := Iff.of_eq (DFunLike.congr_fun heq a)
  have hba : P ((swap a b)⁻¹ • a) := hp.mpr ha
  exact hb (by simpa using hba)

theorem supported_finite_or_cofinite :
    letI : Nominal α Prop := propNominal
    ∀ P : NFun α α Prop, Set.Finite {a | P a} ∨ Set.Finite {a | ¬ P a} := by
  let : Nominal α Prop := propNominal
  intro P
  classical
  by_cases hP : Set.Finite {a | P a}
  · exact Or.inl hP
  · right
    by_contra hNotP
    exact infinite_coinfinite_unsupported P hP hNotP P.finSupp_toPFun

theorem supported_fresh_neg :
    letI : Nominal α Prop := propNominal
    ∀ P : NFun α α Prop, (¬ (И a, P a)) ↔ (И a, ¬ P a) := by
  let : Nominal α Prop := propNominal
  intro P
  exact freshQuantifier_neg (supported_finite_or_cofinite P)

omit [Name α] in
theorem unsupported_fresh_neg_fails (P : α → Prop)
    (hP : Set.Infinite {a | P a}) (hNotP : Set.Infinite {a | ¬ P a}) :
    ¬ ((¬ (И a, P a)) ↔ (И a, ¬ P a)) := by
  intro h
  exact hP (freshQuantifier_not.mp (h.mp (fun h' => hNotP (freshQuantifier_iff.mp h'))))

-- Pointwise action on bare predicates differs from conjugation.
example (π : FinitePerm α) (P : X → Prop) (x : X) :
    letI : Nominal α Prop := propNominal
    (π • P) x = P x := rfl
example (π : FinitePerm α) (P : PFun α X Prop) (x : X) :
    letI : Nominal α Prop := propNominal
    (π • P) x = P (π⁻¹ • x) := rfl

#print axioms supportedSubsetEquiv
#print axioms supports_and
#print axioms supports_forall
#print axioms supports_exists
#print axioms supportedSubset_image
#print axioms infinite_coinfinite_unsupported
#print axioms supported_fresh_neg
#print axioms unsupported_fresh_neg_fails
end Predicates

section QuotientSupport
variable {α X : Type u} [Name α] [PermType α X]
variable (s : Setoid X) [IsEquivariantSetoid α X s]

theorem supports_pullback_iff (S : Finset α) (P : Quotient s → Prop) :
    letI : Nominal α Prop := propNominal
    supports S (PFun.mk P : PFun α (Quotient s) Prop) ↔
      supports S (PFun.mk (fun x => P (Quotient.mk s x)) : PFun α X Prop) := by
  let : Nominal α Prop := propNominal
  constructor
  · intro h π hπ
    apply PFun.ext
    intro x
    exact DFunLike.congr_fun (h π hπ) (Quotient.mk s x)
  · intro h π hπ
    apply PFun.ext
    intro q
    induction q using Quotient.ind with
    | _ x => exact DFunLike.congr_fun (h π hπ) x

#print axioms supports_pullback_iff
end QuotientSupport

section BadRawPredicate
open LambdaCalculus
variable {α : Type u} [Name α]

def rootBinderIs (a : α) : LamTerm α → Prop
  | .lam ⟨b, _⟩ => b = a
  | _ => False

theorem rootBinder_cannot_descend (a b : α) (hab : a ≠ b) :
    ¬ ∃ P : Term α → Prop, ∀ t : LamTerm α, P (Quotient.mk _ t) ↔ rootBinderIs a t := by
  rintro ⟨P, hP⟩
  have haeq : AEq (.lam ⟨a, .var a⟩) (.lam ⟨b, .var b⟩) := by
    apply AEq.lam ∅
    intro c _
    simp
  have h := (hP (.lam ⟨a, .var a⟩)).mpr rfl
  rw [Quotient.sound haeq] at h
  exact hab ((hP (.lam ⟨b, .var b⟩)).mp h).symm

#print axioms rootBinder_cannot_descend
end BadRawPredicate
end PredicateFoundations
