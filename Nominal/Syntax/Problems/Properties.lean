import Nominal.Syntax.Problems.Basic

namespace Nominal

open Core

variable {F X 𝔸 : Type*} [DecidableEq F] [DecidableEq X] [Name 𝔸]


/-- A constraint is *reduced* iff it has the form `a #? X` for an unconstrained metavariable. -/
def Constraint.IsReduced : Constraint F X 𝔸 → Bool
  | .fresh _ (.mvar [] _) => True
  | _                     => False

/-- A problem is reduced iff every constraint in it is reduced. -/
def Problem.IsReduced (Q : Problem F X 𝔸) : Prop :=
  ∀ c ∈ Q, c.IsReduced

lemma Problem.IsReduced.nil : Problem.IsReduced ([] : Problem F X 𝔸) := by
  intro c hc; cases hc

lemma Problem.IsReduced.append {Q₁ Q₂ : Problem F X 𝔸}
    (h₁ : Q₁.IsReduced) (h₂ : Q₂.IsReduced) : (Q₁ ++ Q₂).IsReduced := by
  intro c hc
  rcases List.mem_append.mp hc with h | h
  · exact h₁ c h
  · exact h₂ c h


mutual
  /-- `simplifyFresh` produces a reduced problem whenever it succeeds. -/
  lemma simplifyFresh_isReduced (a : 𝔸) (t : ntm F X 𝔸) {Q : Problem F X 𝔸}
      (h : simplifyFresh a t = some Q) : Q.IsReduced :=
    match t, h with
    | .atm b, h => by
        simp only [simplifyFresh] at h
        split_ifs at h with hab
        injection h with heq; subst heq
        exact Problem.IsReduced.nil
    | .mvar π x, h => by
        simp only [simplifyFresh] at h
        injection h with heq; subst heq
        intro c hc
        simp only [List.mem_singleton] at hc
        subst hc
        trivial
    | .fapp _ ts, h => by
        simp only [simplifyFresh] at h
        exact simplifyFreshList_isReduced a ts h
    | .abs b t', h => by
        simp only [simplifyFresh] at h
        split_ifs at h with hab
        · injection h with heq; subst heq; exact Problem.IsReduced.nil
        · exact simplifyFresh_isReduced a t' h

  /-- `simplifyFreshList` produces a reduced problem whenever it succeeds. -/
  lemma simplifyFreshList_isReduced (a : 𝔸) (ts : List (ntm F X 𝔸)) {Q : Problem F X 𝔸}
      (h : simplifyFreshList a ts = some Q) : Q.IsReduced :=
    match ts, h with
    | [], h => by
        simp only [simplifyFreshList] at h
        injection h with heq; subst heq
        exact Problem.IsReduced.nil
    | t :: ts', h => by
        simp only [simplifyFreshList] at h
        cases hf : simplifyFresh a t with
        | none => rw [hf] at h; cases h
        | some cs₁ =>
          cases hl : simplifyFreshList a ts' with
          | none => rw [hf, hl] at h; cases h
          | some cs₂ =>
            rw [hf, hl] at h
            injection h with heq; subst heq
            exact Problem.IsReduced.append
              (simplifyFresh_isReduced a t hf)
              (simplifyFreshList_isReduced a ts' hl)
end

mutual
  /-- `simplifyAlpha` produces a reduced problem whenever it succeeds. -/
  lemma simplifyAlpha_isReduced (s t : ntm F X 𝔸) {Q : Problem F X 𝔸}
      (h : simplifyAlpha s t = some Q) : Q.IsReduced :=
    match s, t, h with
    | .atm a, .atm b, h => by
        simp only [simplifyAlpha] at h
        split_ifs at h with hab
        injection h with heq; subst heq
        exact Problem.IsReduced.nil
    | .mvar π x, .mvar π' y, h => by
        simp only [simplifyAlpha] at h
        split_ifs at h with hxy
        injection h with heq; subst heq
        intro c hc
        rcases List.mem_map.mp hc with ⟨n, _, rfl⟩
        trivial
    | .fapp f ls, .fapp g ss, h => by
        simp only [simplifyAlpha] at h
        split_ifs at h with hfg
        exact simplifyAlphaList_isReduced ls ss h
    | .abs a l, .abs b s', h => by
        simp only [simplifyAlpha] at h
        split_ifs at h with hab
        · exact simplifyAlpha_isReduced l s' h
        · cases h₁ : simplifyAlpha (l.permute [(b, a)]) s' with
          | none => rw [h₁] at h; cases h
          | some cs₁ =>
            cases h₂ : simplifyFresh b l with
            | none => rw [h₁, h₂] at h; cases h
            | some cs₂ =>
              rw [h₁, h₂] at h
              injection h with heq; subst heq
              exact Problem.IsReduced.append
                (simplifyAlpha_isReduced _ _ h₁)
                (simplifyFresh_isReduced b l h₂)
    | .atm _,    .mvar _ _, h | .atm _,    .fapp _ _, h | .atm _,    .abs _ _, h
    | .mvar _ _, .atm _,    h | .mvar _ _, .fapp _ _, h | .mvar _ _, .abs _ _, h
    | .fapp _ _, .atm _,    h | .fapp _ _, .mvar _ _, h | .fapp _ _, .abs _ _, h
    | .abs _ _,  .atm _,    h | .abs _ _,  .mvar _ _, h | .abs _ _,  .fapp _ _, h => by
        simp [simplifyAlpha] at h

  /-- `simplifyAlphaList` produces a reduced problem whenever it succeeds. -/
  lemma simplifyAlphaList_isReduced (ls ss : List (ntm F X 𝔸)) {Q : Problem F X 𝔸}
      (h : simplifyAlphaList ls ss = some Q) : Q.IsReduced :=
    match ls, ss, h with
    | [], [], h => by
        simp only [simplifyAlphaList] at h
        injection h with heq; subst heq
        exact Problem.IsReduced.nil
    | l :: ls', s :: ss', h => by
        simp only [simplifyAlphaList] at h
        cases h₁ : simplifyAlpha l s with
        | none => rw [h₁] at h; cases h
        | some cs₁ =>
          cases h₂ : simplifyAlphaList ls' ss' with
          | none => rw [h₁, h₂] at h; cases h
          | some cs₂ =>
            rw [h₁, h₂] at h
            injection h with heq; subst heq
            exact Problem.IsReduced.append
              (simplifyAlpha_isReduced l s h₁)
              (simplifyAlphaList_isReduced ls' ss' h₂)
    | [], _ :: _, h => by simp [simplifyAlphaList] at h
    | _ :: _, [], h => by simp [simplifyAlphaList] at h
end

/-- The top-level simplifier produces a reduced problem whenever it succeeds. -/
lemma simplify_isReduced : ∀ (P : Problem F X 𝔸) {Q : Problem F X 𝔸},
    simplify P = some Q → Q.IsReduced
  | [], Q, h => by
      simp only [simplify] at h
      injection h with heq; subst heq
      exact Problem.IsReduced.nil
  | .fresh a t :: rest, Q, h => by
      simp only [simplify] at h
      cases h₁ : simplifyFresh a t with
      | none => rw [h₁] at h; cases h
      | some cs₁ =>
        cases h₂ : simplify rest with
        | none => rw [h₁, h₂] at h; cases h
        | some cs₂ =>
          rw [h₁, h₂] at h
          injection h with heq; subst heq
          exact Problem.IsReduced.append
            (simplifyFresh_isReduced a t h₁)
            (simplify_isReduced rest h₂)
  | .alpha s t :: rest, Q, h => by
      simp only [simplify] at h
      cases h₁ : simplifyAlpha s t with
      | none => rw [h₁] at h; cases h
      | some cs₁ =>
        cases h₂ : simplify rest with
        | none => rw [h₁, h₂] at h; cases h
        | some cs₂ =>
          rw [h₁, h₂] at h
          injection h with heq; subst heq
          exact Problem.IsReduced.append
            (simplifyAlpha_isReduced s t h₁)
            (simplify_isReduced rest h₂)


/-- A context entails a constraint when the constraint is satisfied. -/
def Constraint.Entails (Γ : Context 𝔸 X) : Constraint F X 𝔸 → Bool
  | .fresh a t => Nominal.fresh Γ a t
  | .alpha s t => Nominal.alphaEquiv Γ s t

/-- A context entails a problem when it entails every constraint. -/
def Problem.Entails (Γ : Context 𝔸 X) (P : Problem F X 𝔸) : Prop :=
  ∀ c ∈ P, c.Entails Γ

lemma Problem.Entails.nil {Γ : Context 𝔸 X} : Problem.Entails Γ ([] : Problem F X 𝔸) := by
  intro c hc; cases hc

lemma Problem.Entails_append_iff {Γ : Context 𝔸 X} {P Q : Problem F X 𝔸} :
    Problem.Entails Γ (P ++ Q) ↔ Problem.Entails Γ P ∧ Problem.Entails Γ Q := by
  constructor
  · intro h
    refine ⟨fun c hc => h c (List.mem_append.mpr (Or.inl hc)),
            fun c hc => h c (List.mem_append.mpr (Or.inr hc))⟩
  · rintro ⟨h1, h2⟩ c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc


mutual
  /-- Soundness for `simplifyFresh`: a successful simplification preserves the freshness judgement. -/
  lemma simplifyFresh_sound (Γ : Context 𝔸 X) (a : 𝔸) (t : ntm F X 𝔸) {Q : Problem F X 𝔸}
      (h : simplifyFresh a t = some Q) : (Γ ⊢ a # t) ↔ Problem.Entails Γ Q :=
    match t, h with
    | .atm b, h => by
        simp only [simplifyFresh] at h
        split_ifs at h with hab
        injection h with heq; subst heq
        simp [fresh, hab, Problem.Entails.nil]
    | .mvar π x, h => by
        simp only [simplifyFresh] at h
        injection h with heq; subst heq
        simp only [fresh, Problem.Entails, List.mem_singleton, forall_eq,
                   Constraint.Entails, List.reverse_nil, LPermApply_nil]
    | .fapp _ ts, h => by
        simp only [simplifyFresh] at h
        show (freshList Γ a ts) ↔ Problem.Entails Γ Q
        exact simplifyFreshList_sound Γ a ts h
    | .abs b t', h => by
        simp only [simplifyFresh] at h
        split_ifs at h with hab
        · injection h with heq; subst heq
          subst hab
          simp [fresh, Problem.Entails.nil]
        · have ih := simplifyFresh_sound Γ a t' h
          simp only [fresh, decide_eq_true_eq]
          constructor
          · rintro (h_eq | h')
            · exact absurd h_eq hab
            · exact ih.mp h'
          · intro hQ
            exact Or.inr (ih.mpr hQ)

  /-- Soundness for `simplifyFreshList`. -/
  lemma simplifyFreshList_sound (Γ : Context 𝔸 X) (a : 𝔸) (ts : List (ntm F X 𝔸))
      {Q : Problem F X 𝔸} (h : simplifyFreshList a ts = some Q) :
      (freshList Γ a ts) ↔ Problem.Entails Γ Q :=
    match ts, h with
    | [], h => by
        simp only [simplifyFreshList] at h
        injection h with heq; subst heq
        simp [freshList, Problem.Entails.nil]
    | t :: ts', h => by
        simp only [simplifyFreshList] at h
        cases hf : simplifyFresh a t with
        | none => rw [hf] at h; cases h
        | some cs₁ =>
          cases hl : simplifyFreshList a ts' with
          | none => rw [hf, hl] at h; cases h
          | some cs₂ =>
            rw [hf, hl] at h
            injection h with heq; subst heq
            have ih₁ := simplifyFresh_sound Γ a t hf
            have ih₂ := simplifyFreshList_sound Γ a ts' hl
            simp only [freshList, decide_eq_true_eq, Problem.Entails_append_iff]
            exact and_congr ih₁ ih₂
end

mutual
  /-- Soundness for `simplifyAlpha`. -/
  lemma simplifyAlpha_sound (Γ : Context 𝔸 X) (s t : ntm F X 𝔸) {Q : Problem F X 𝔸}
      (h : simplifyAlpha s t = some Q) : (Γ ⊢ s ≈α t) ↔ Problem.Entails Γ Q :=
    match s, t, h with
    | .atm a, .atm b, h => by
        simp only [simplifyAlpha] at h
        split_ifs at h with hab
        injection h with heq; subst heq; subst hab
        simp [alphaEquiv, Problem.Entails.nil]
    | .mvar π x, .mvar π' y, h => by
        simp only [simplifyAlpha] at h
        split_ifs at h with hxy
        injection h with heq; subst heq; subst hxy
        constructor
        · intro hL c hc
          simp only [List.mem_map] at hc
          obtain ⟨n, hn, rfl⟩ := hc
          show (Γ ⊢ n # ntm.mvar (F := F) [] x) = true
          simp only [fresh, List.reverse_nil, LPermApply_nil, decide_eq_true_eq]
          simp only [alphaEquiv, decide_eq_true_eq, true_and] at hL
          exact hL n ((mem_dsList_iff_mem_ds n π π').mp hn)
        · intro hR
          simp only [alphaEquiv, decide_eq_true_eq, true_and]
          intro n hn
          have hc : (Constraint.fresh n (ntm.mvar (F := F) [] x)) ∈
              (dsList π π').map (fun n => Constraint.fresh n (ntm.mvar [] x)) :=
            List.mem_map.mpr ⟨n, (mem_dsList_iff_mem_ds n π π').mpr hn, rfl⟩
          have hE := hR _ hc
          show (n, x) ∈ Γ
          simp only [Constraint.Entails, fresh, List.reverse_nil, LPermApply_nil,
                     decide_eq_true_eq] at hE
          exact hE
    | .fapp f ls, .fapp g ss, h => by
        simp only [simplifyAlpha] at h
        split_ifs at h with hfg
        subst hfg
        simp only [alphaEquiv, decide_eq_true_eq, true_and]
        exact simplifyAlphaList_sound Γ ls ss h
    | .abs a l, .abs b s', h => by
        simp only [simplifyAlpha] at h
        split_ifs at h with hab
        · subst hab
          simp only [alphaEquiv]
          show (alphaEquiv Γ l s' = true) ↔ Problem.Entails Γ Q
          exact simplifyAlpha_sound Γ l s' h
        · cases h₁ : simplifyAlpha (l.permute [(b, a)]) s' with
          | none => rw [h₁] at h; cases h
          | some cs₁ =>
            cases h₂ : simplifyFresh b l with
            | none => rw [h₁, h₂] at h; cases h
            | some cs₂ =>
              rw [h₁, h₂] at h
              injection h with heq; subst heq
              simp only [alphaEquiv, if_neg hab, decide_eq_true_eq,
                         Problem.Entails_append_iff]
              exact and_congr (simplifyAlpha_sound Γ _ _ h₁) (simplifyFresh_sound Γ b l h₂)
    | .atm _,    .mvar _ _, h | .atm _,    .fapp _ _, h | .atm _,    .abs _ _, h
    | .mvar _ _, .atm _,    h | .mvar _ _, .fapp _ _, h | .mvar _ _, .abs _ _, h
    | .fapp _ _, .atm _,    h | .fapp _ _, .mvar _ _, h | .fapp _ _, .abs _ _, h
    | .abs _ _,  .atm _,    h | .abs _ _,  .mvar _ _, h | .abs _ _,  .fapp _ _, h => by
        simp [simplifyAlpha] at h

  /-- Soundness for `simplifyAlphaList`. -/
  lemma simplifyAlphaList_sound (Γ : Context 𝔸 X) (ls ss : List (ntm F X 𝔸))
      {Q : Problem F X 𝔸} (h : simplifyAlphaList ls ss = some Q) :
      (alphaEquivList Γ ls ss) ↔ Problem.Entails Γ Q :=
    match ls, ss, h with
    | [], [], h => by
        simp only [simplifyAlphaList] at h
        injection h with heq; subst heq
        simp [alphaEquivList, Problem.Entails.nil]
    | l :: ls', s :: ss', h => by
        simp only [simplifyAlphaList] at h
        cases h₁ : simplifyAlpha l s with
        | none => rw [h₁] at h; cases h
        | some cs₁ =>
          cases h₂ : simplifyAlphaList ls' ss' with
          | none => rw [h₁, h₂] at h; cases h
          | some cs₂ =>
            rw [h₁, h₂] at h
            injection h with heq; subst heq
            have ih₁ := simplifyAlpha_sound Γ l s h₁
            have ih₂ := simplifyAlphaList_sound Γ ls' ss' h₂
            simp only [alphaEquivList, decide_eq_true_eq, Problem.Entails_append_iff]
            exact and_congr ih₁ ih₂
    | [], _ :: _, h => by simp [simplifyAlphaList] at h
    | _ :: _, [], h => by simp [simplifyAlphaList] at h
end

/-- Soundness for the top-level simplifier: if `simplify P = some Q`, then a context entails
    `P` exactly when it entails `Q`. -/
lemma simplify_sound (Γ : Context 𝔸 X) : ∀ (P : Problem F X 𝔸) {Q : Problem F X 𝔸},
    simplify P = some Q → (Problem.Entails Γ P ↔ Problem.Entails Γ Q)
  | [], Q, h => by
      simp only [simplify] at h
      injection h with heq; subst heq
      trivial
  | .fresh a t :: rest, Q, h => by
      simp only [simplify] at h
      cases h₁ : simplifyFresh a t with
      | none => rw [h₁] at h; cases h
      | some cs₁ =>
        cases h₂ : simplify rest with
        | none => rw [h₁, h₂] at h; cases h
        | some cs₂ =>
          rw [h₁, h₂] at h
          injection h with heq; subst heq
          rw [show ((Constraint.fresh a t :: rest) : Problem F X 𝔸) = [.fresh a t] ++ rest from rfl]
          rw [Problem.Entails_append_iff, Problem.Entails_append_iff]
          refine and_congr ?_ (simplify_sound Γ rest h₂)
          constructor
          · intro hP
            exact (simplifyFresh_sound Γ a t h₁).mp
              (by simpa [Problem.Entails, Constraint.Entails] using hP)
          · intro hQ c hc
            simp only [List.mem_singleton] at hc
            subst hc
            exact (simplifyFresh_sound Γ a t h₁).mpr hQ
  | .alpha s t :: rest, Q, h => by
      simp only [simplify] at h
      cases h₁ : simplifyAlpha s t with
      | none => rw [h₁] at h; cases h
      | some cs₁ =>
        cases h₂ : simplify rest with
        | none => rw [h₁, h₂] at h; cases h
        | some cs₂ =>
          rw [h₁, h₂] at h
          injection h with heq; subst heq
          rw [show ((Constraint.alpha s t :: rest) : Problem F X 𝔸) = [.alpha s t] ++ rest from rfl]
          rw [Problem.Entails_append_iff, Problem.Entails_append_iff]
          refine and_congr ?_ (simplify_sound Γ rest h₂)
          constructor
          · intro hP
            exact (simplifyAlpha_sound Γ s t h₁).mp
              (by simpa [Problem.Entails, Constraint.Entails] using hP)
          · intro hQ c hc
            simp only [List.mem_singleton] at hc
            subst hc
            exact (simplifyAlpha_sound Γ s t h₁).mpr hQ

end Nominal
