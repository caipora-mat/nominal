import Nominal.Syntax.Terms

namespace Nominal

open Core

variable {F X 𝔸 : Type*} [DecidableEq F] [DecidableEq X] [Name 𝔸]

-- (Atoms of a permutation and difference list).

/-- Computable list of atoms in a permutation. -/
def LPerm.atomsList : LPerm 𝔸 → List 𝔸
  | []           => []
  | (a, b) :: ps => a :: b :: LPerm.atomsList ps

/-- Computable difference list (may contain duplicates). -/
def dsList (π π' : LPerm 𝔸) : List 𝔸 :=
  (LPerm.atomsList π ++ LPerm.atomsList π').filter fun n =>
    LPermApply π n ≠ LPermApply π' n

-- (Constraints and problems).

/-- A constraint is either a freshness question `a #? t` or an alpha-equivalence question `s ≈α? t`. -/
inductive Constraint (F X 𝔸 : Type*) [DecidableEq F] [DecidableEq X] [Name 𝔸] where
  | fresh : 𝔸 → ntm F X 𝔸 → Constraint F X 𝔸
  | alpha : ntm F X 𝔸 → ntm F X 𝔸 → Constraint F X 𝔸

/-- A constraint problem is a list of constraints. -/
abbrev Problem (F X 𝔸 : Type*) [DecidableEq F] [DecidableEq X] [Name 𝔸] :=
  List (Constraint F X 𝔸)

-- (Freshness simplification).

mutual
  /-- Simplify `a # t` to a list of reduced constraints. -/
  def simplifyFresh (a : 𝔸) : ntm F X 𝔸 → Option (Problem F X 𝔸)
    | .atm b     => if a = b then none else some []
    | .abs b t   => if a = b then some [] else simplifyFresh a t
    | .mvar π x  => some [.fresh (LPermApply π.reverse a) (.mvar [] x)]
    | .fapp _ ts => simplifyFreshList a ts

  def simplifyFreshList (a : 𝔸) : List (ntm F X 𝔸) → Option (Problem F X 𝔸)
    | []      => some []
    | t :: ts =>
      match simplifyFresh a t, simplifyFreshList a ts with
      | some cs₁, some cs₂ => some (cs₁ ++ cs₂)
      | _, _               => none
end

-- (Alpha-equivalence simplification).

mutual
  /-- Simplify `s ≈α t` to a list of reduced constraints. -/
  def simplifyAlpha : ntm F X 𝔸 → ntm F X 𝔸 → Option (Problem F X 𝔸)
    | .atm a, .atm b =>
        if a = b then some [] else none
    | .mvar π x, .mvar π' y =>
        if x = y then some ((dsList π π').map fun n => .fresh n (.mvar [] x))
        else none
    | .fapp f ls, .fapp g ss =>
        if f = g then simplifyAlphaList ls ss else none
    | .abs a l, .abs b s =>
        if a = b then simplifyAlpha l s
        else
          match simplifyAlpha (l.permute [(b, a)]) s, simplifyFresh b l with
          | some cs₁, some cs₂ => some (cs₁ ++ cs₂)
          | _, _               => none
    | _, _ => none

  def simplifyAlphaList : List (ntm F X 𝔸) → List (ntm F X 𝔸) → Option (Problem F X 𝔸)
    | [], []         => some []
    | l :: ls, s :: ss =>
      match simplifyAlpha l s, simplifyAlphaList ls ss with
      | some cs₁, some cs₂ => some (cs₁ ++ cs₂)
      | _, _               => none
    | _, _ => none
end

-- (Top-level simplifier).

/-- Simplify each constraint to reduced form; `none` if any is inconsistent. -/
def simplify : Problem F X 𝔸 → Option (Problem F X 𝔸)
  | []                 => some []
  | .fresh a t :: rest =>
    match simplifyFresh a t, simplify rest with
    | some cs₁, some cs₂ => some (cs₁ ++ cs₂)
    | _, _               => none
  | .alpha s t :: rest =>
    match simplifyAlpha s t, simplify rest with
    | some cs₁, some cs₂ => some (cs₁ ++ cs₂)
    | _, _               => none

-- (Reduced form).

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

-- (Normalization).

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








end Nominal
