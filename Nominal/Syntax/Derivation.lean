import Nominal.Syntax.AlphaEquiv.Basic

/-!
# Freshness and α-equivalence as inference rules

`fresh` and `alphaEquiv` are `Bool`-valued functions. This file gives the
rule-based presentation of the same relations as inductive predicates, one
constructor per inference rule, and proves that each predicate holds exactly
when the corresponding function returns `true` (reflection).
-/

namespace Nominal

open Core

variable {F X 𝔸 : Type*} [DecidableEq F] [DecidableEq X] [Name 𝔸]

/-- Derivable freshness `Γ ⊢ a # t`, one constructor per freshness rule. -/
inductive Fresh (Γ : Context 𝔸 X) (a : 𝔸) : ntm F X 𝔸 → Prop
  /-- (#atom) -/
  | atom {b : 𝔸} : a ≠ b → Fresh Γ a (.atm b)
  /-- (#var) -/
  | var {π : LPerm 𝔸} {x : X} :
      (LPermApply π.reverse a, x) ∈ Γ → Fresh Γ a (.mvar π x)
  /-- (#abs1) -/
  | abs1 {t : ntm F X 𝔸} : Fresh Γ a (.abs a t)
  /-- (#abs2) -/
  | abs2 {b : 𝔸} {t : ntm F X 𝔸} : a ≠ b → Fresh Γ a t → Fresh Γ a (.abs b t)
  /-- (#app) -/
  | app {f : F} {ts : List (ntm F X 𝔸)} :
      (∀ t ∈ ts, Fresh Γ a t) → Fresh Γ a (.fapp f ts)

mutual
  /-- Derivable α-equivalence `Γ ⊢ s ≈α t`, one constructor per α-equivalence rule. -/
  inductive AlphaEq (Γ : Context 𝔸 X) : ntm F X 𝔸 → ntm F X 𝔸 → Prop
    /-- (eq-atom) -/
    | atom (a : 𝔸) : AlphaEq Γ (.atm a) (.atm a)
    /-- (eq-var) -/
    | var {π π' : LPerm 𝔸} {x : X} :
        (∀ n ∈ ds π π', (n, x) ∈ Γ) → AlphaEq Γ (.mvar π x) (.mvar π' x)
    /-- (eq-abs1) -/
    | abs1 {a : 𝔸} {s t : ntm F X 𝔸} :
        AlphaEq Γ s t → AlphaEq Γ (.abs a s) (.abs a t)
    /-- (eq-abs2) -/
    | abs2 {a b : 𝔸} {s t : ntm F X 𝔸} :
        a ≠ b → AlphaEq Γ (s.permute [(b, a)]) t → Fresh Γ b s →
        AlphaEq Γ (.abs a s) (.abs b t)
    /-- (eq-app) -/
    | app {f : F} {ss ts : List (ntm F X 𝔸)} :
        AlphaEqList Γ ss ts → AlphaEq Γ (.fapp f ss) (.fapp f ts)

  /-- Pointwise `AlphaEq` on argument lists of the same length. -/
  inductive AlphaEqList (Γ : Context 𝔸 X) : List (ntm F X 𝔸) → List (ntm F X 𝔸) → Prop
    | nil : AlphaEqList Γ [] []
    | cons {s t : ntm F X 𝔸} {ss ts : List (ntm F X 𝔸)} :
        AlphaEq Γ s t → AlphaEqList Γ ss ts → AlphaEqList Γ (s :: ss) (t :: ts)
end

mutual
  /-- Reflection for freshness: the function `fresh` decides `Fresh`. -/
  theorem fresh_iff_Fresh (Γ : Context 𝔸 X) (a : 𝔸) (t : ntm F X 𝔸) :
      (Γ ⊢ a # t) = true ↔ Fresh Γ a t := by
    match t with
    | .atm b =>
      simp only [fresh, ne_eq, decide_eq_true_eq]
      constructor
      · exact Fresh.atom
      · intro h; cases h with | atom h => exact h
    | .mvar π x =>
      simp only [fresh, decide_eq_true_eq]
      constructor
      · exact Fresh.var
      · intro h; cases h with | var h => exact h
    | .fapp f ts =>
      simp only [fresh]
      rw [freshList_iff_Fresh Γ a ts]
      constructor
      · exact Fresh.app
      · intro h; cases h with | app h => exact h
    | .abs b t =>
      simp only [fresh, Bool.decide_or, Bool.or_eq_true, decide_eq_true_eq]
      rw [fresh_iff_Fresh Γ a t]
      constructor
      · rintro (rfl | h)
        · exact Fresh.abs1
        · by_cases hab : a = b
          · subst hab; exact Fresh.abs1
          · exact Fresh.abs2 hab h
      · intro h
        cases h with
        | abs1 => exact Or.inl rfl
        | abs2 _ h => exact Or.inr h

  theorem freshList_iff_Fresh (Γ : Context 𝔸 X) (a : 𝔸) (ts : List (ntm F X 𝔸)) :
      freshList Γ a ts = true ↔ ∀ t ∈ ts, Fresh Γ a t := by
    match ts with
    | [] => simp [freshList]
    | t :: ts =>
      simp only [freshList, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq,
        List.forall_mem_cons]
      rw [fresh_iff_Fresh Γ a t, freshList_iff_Fresh Γ a ts]
end

mutual
  /-- Reflection for α-equivalence: the function `alphaEquiv` decides `AlphaEq`. -/
  theorem alphaEquiv_iff_AlphaEq (Γ : Context 𝔸 X) (s t : ntm F X 𝔸) :
      (Γ ⊢ s ≈α t) = true ↔ AlphaEq Γ s t := by
    match s, t with
    | .atm a, .atm b =>
      simp only [alphaEquiv, decide_eq_true_eq]
      constructor
      · rintro rfl; exact AlphaEq.atom a
      · intro h; cases h; rfl
    | .mvar π x, .mvar π' y =>
      simp only [alphaEquiv, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨rfl, h⟩; exact AlphaEq.var h
      · intro h; cases h with | var h => exact ⟨rfl, h⟩
    | .fapp f ss, .fapp g ts =>
      simp only [alphaEquiv, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq]
      rw [alphaEquivList_iff_AlphaEqList Γ ss ts]
      constructor
      · rintro ⟨rfl, h⟩; exact AlphaEq.app h
      · intro h; cases h with | app h => exact ⟨rfl, h⟩
    | .abs a s, .abs b t =>
      by_cases hab : a = b
      · subst hab
        simp only [alphaEquiv, if_pos]
        rw [alphaEquiv_iff_AlphaEq Γ s t]
        constructor
        · exact AlphaEq.abs1
        · intro h
          cases h with
          | abs1 h => exact h
          | abs2 hne _ _ => exact absurd rfl hne
      · simp only [alphaEquiv, if_neg hab, Bool.decide_and, Bool.and_eq_true,
          decide_eq_true_eq]
        rw [alphaEquiv_iff_AlphaEq Γ (s.permute [(b, a)]) t, fresh_iff_Fresh]
        constructor
        · rintro ⟨h₁, h₂⟩; exact AlphaEq.abs2 hab h₁ h₂
        · intro h
          cases h with
          | abs1 _ => exact absurd rfl hab
          | abs2 _ h₁ h₂ => exact ⟨h₁, h₂⟩
    | .atm _, .mvar _ _ | .atm _, .fapp _ _ | .atm _, .abs _ _
    | .mvar _ _, .atm _ | .mvar _ _, .fapp _ _ | .mvar _ _, .abs _ _
    | .fapp _ _, .atm _ | .fapp _ _, .mvar _ _ | .fapp _ _, .abs _ _
    | .abs _ _, .atm _ | .abs _ _, .mvar _ _ | .abs _ _, .fapp _ _ =>
      simp only [alphaEquiv, Bool.false_eq_true, false_iff]
      intro h; cases h
  termination_by ntmSize s
  decreasing_by all_goals simp [ntmSize, ntmPermSize]

  theorem alphaEquivList_iff_AlphaEqList (Γ : Context 𝔸 X) (ss ts : List (ntm F X 𝔸)) :
      alphaEquivList Γ ss ts = true ↔ AlphaEqList Γ ss ts := by
    match ss, ts with
    | [], [] => simp only [alphaEquivList, true_iff]; exact AlphaEqList.nil
    | s :: ss, t :: ts =>
      simp only [alphaEquivList, Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq]
      rw [alphaEquiv_iff_AlphaEq Γ s t, alphaEquivList_iff_AlphaEqList Γ ss ts]
      constructor
      · rintro ⟨h₁, h₂⟩; exact AlphaEqList.cons h₁ h₂
      · intro h; cases h with | cons h₁ h₂ => exact ⟨h₁, h₂⟩
    | [], _ :: _ | _ :: _, [] =>
      simp only [alphaEquivList, Bool.false_eq_true, false_iff]
      intro h; cases h
  termination_by ntmSize.ntmSizeList ss
  decreasing_by
    all_goals simp [ntmSize.ntmSizeList]
    all_goals omega
end

end Nominal
