import Nominal.Syntax.Unification.Basic
import Nominal.Syntax.Problems.Basic

namespace Nominal

open Core

variable {F X 𝔸 : Type*} [DecidableEq F] [DecidableEq X] [Name 𝔸]


def Constraint.toUnif : Constraint F X 𝔸 → UnifConstraint F X 𝔸
  | .fresh a t => .fresh a t
  | .alpha s t => .unif s t


inductive StepResult (F X 𝔸 : Type*) [DecidableEq F] [DecidableEq X] [Name 𝔸] where
  | fail : StepResult F X 𝔸
  | ctx  : 𝔸 → X → StepResult F X 𝔸
  | next : UnifProblem F X 𝔸 → Subst F X 𝔸 → StepResult F X 𝔸


def unifStep (c : UnifConstraint F X 𝔸) (rest : UnifProblem F X 𝔸) (σ : Subst F X 𝔸) :
    StepResult F X 𝔸 :=
  match c with
  | .fresh b (.mvar π x) =>
      .ctx (LPermApply π.reverse b) x
  | .fresh a t =>
      match simplifyFresh a t with
      | none    => .fail
      | some cs => .next (rest ++ cs.map (·.toUnif)) σ
  | .unif s t =>
      match s, t with
      | .atm a, .atm b =>
          if a = b then .next rest σ else .fail
      | .mvar π x, .mvar π' y =>
          if x = y then
            .next (rest ++ (dsList π π').map (UnifConstraint.fresh · (.mvar [] x))) σ
          else
            let binding := (x, (ntm.mvar π' y : ntm F X 𝔸).permute π.reverse)
            .next (rest.applySubst [binding]) (σ.comp [binding])
      | .mvar π x, u =>
          if u.occursIn x then .fail
          else
            let binding := (x, u.permute π.reverse)
            .next (rest.applySubst [binding]) (σ.comp [binding])
      | u, .mvar π x =>
          if u.occursIn x then .fail
          else
            let binding := (x, u.permute π.reverse)
            .next (rest.applySubst [binding]) (σ.comp [binding])
      | .fapp f ss, .fapp g ts =>
          if f = g ∧ ss.length = ts.length then
              .next ((ss.zip ts).map (fun (s, t) => .unif s t) ++ rest) σ
          else .fail
      | .abs a s', .abs b t' =>
          if a = b then
            .next (.unif s' t' :: rest) σ
          else
            .next (.unif (s'.permute [(b, a)]) t' :: .fresh b s' :: rest) σ
      | _, _ => .fail

lemma unifStep_fresh_of_not_mvar (a : 𝔸) (t : ntm F X 𝔸) (rest : UnifProblem F X 𝔸)
    (σ : Subst F X 𝔸) (ht : ∀ π x, t ≠ .mvar π x) :
    unifStep (.fresh a t) rest σ =
      match simplifyFresh a t with
      | none    => .fail
      | some cs => .next (rest ++ cs.map (·.toUnif)) σ := by
  cases t with
  | mvar π x => exact absurd rfl (ht π x)
  | _ => rfl

/-- The rewrite rules behind the `.next` outcomes of `unifStep`: `UnifRule rest σ c Pr' σ'` says
    that the head constraint `c` is replaced, turning `(c :: rest, σ)` into `(Pr', σ')`. -/
inductive UnifRule (rest : UnifProblem F X 𝔸) (σ : Subst F X 𝔸) :
    UnifConstraint F X 𝔸 → UnifProblem F X 𝔸 → Subst F X 𝔸 → Prop where
  /-- `a #? t` with `t` not a suspension: reduce to primitive freshness constraints. -/
  | fresh (a : 𝔸) (t : ntm F X 𝔸) (cs : Problem F X 𝔸) (ht : ∀ π x, t ≠ .mvar π x)
      (hcs : simplifyFresh a t = some cs) :
      UnifRule rest σ (.fresh a t) (rest ++ cs.map (·.toUnif)) σ
  /-- `a ≈? a`: delete. -/
  | atm (a : 𝔸) : UnifRule rest σ (.unif (.atm a) (.atm a)) rest σ
  /-- `π · X ≈? π' · X`: the atoms of `ds π π'` must be fresh for `X`. -/
  | mvarSame (π π' : LPerm 𝔸) (x : X) :
      UnifRule rest σ (.unif (.mvar π x) (.mvar π' x))
        (rest ++ (dsList π π').map (UnifConstraint.fresh · (.mvar [] x))) σ
  /-- `π · X ≈? u` with `X` not in `u`: instantiate `X ↦ π⁻¹ · u`. -/
  | instL (π : LPerm 𝔸) (x : X) (u : ntm F X 𝔸) (hocc : u.occursIn x = false) :
      UnifRule rest σ (.unif (.mvar π x) u)
        (rest.applySubst [(x, u.permute π.reverse)]) (σ.comp [(x, u.permute π.reverse)])
  /-- `u ≈? π · X` with `X` not in `u`: instantiate `X ↦ π⁻¹ · u`. -/
  | instR (π : LPerm 𝔸) (x : X) (u : ntm F X 𝔸) (hocc : u.occursIn x = false) :
      UnifRule rest σ (.unif u (.mvar π x))
        (rest.applySubst [(x, u.permute π.reverse)]) (σ.comp [(x, u.permute π.reverse)])
  /-- `f ss ≈? f ts`: decompose. -/
  | fapp (f : F) (ss ts : List (ntm F X 𝔸)) (hlen : ss.length = ts.length) :
      UnifRule rest σ (.unif (.fapp f ss) (.fapp f ts))
        ((ss.zip ts).map (fun (s, t) => .unif s t) ++ rest) σ
  /-- `[a]s ≈? [a]t`: unify the bodies. -/
  | absSame (a : 𝔸) (s t : ntm F X 𝔸) :
      UnifRule rest σ (.unif (.abs a s) (.abs a t)) (.unif s t :: rest) σ
  /-- `[a]s ≈? [b]t` with `a ≠ b`: unify `(b a) · s` with `t`, and require `b # s`. -/
  | absDiff (a b : 𝔸) (s t : ntm F X 𝔸) (hab : a ≠ b) :
      UnifRule rest σ (.unif (.abs a s) (.abs b t))
        (.unif (s.permute [(b, a)]) t :: .fresh b s :: rest) σ

/-- Every `.next` outcome of `unifStep` is an instance of one of the rules. -/
theorem UnifRule.of_unifStep {c : UnifConstraint F X 𝔸} {rest : UnifProblem F X 𝔸}
    {σ : Subst F X 𝔸} {Pr' : UnifProblem F X 𝔸} {σ' : Subst F X 𝔸}
    (h : unifStep c rest σ = .next Pr' σ') : UnifRule rest σ c Pr' σ' := by
  cases c with
  | fresh a t =>
    by_cases ht : ∃ π x, t = .mvar π x
    · obtain ⟨π, x, rfl⟩ := ht
      simp [unifStep] at h
    · push_neg at ht
      rw [unifStep_fresh_of_not_mvar _ _ _ _ ht] at h
      cases hcs : simplifyFresh a t with
      | none => simp [hcs] at h
      | some cs =>
        simp only [hcs, StepResult.next.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .fresh a t cs ht hcs
  | unif s t =>
    cases s with
    | atm a =>
      cases t with
      | atm b =>
        simp only [unifStep] at h
        split_ifs at h with hab
        obtain ⟨rfl, rfl⟩ := h
        subst hab
        exact .atm a
      | mvar π x =>
        simp only [unifStep, ntm.occursIn, Bool.false_eq_true, if_false,
          StepResult.next.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .instR π x _ rfl
      | fapp _ _ | abs _ _ => simp [unifStep] at h
    | mvar π x =>
      cases t with
      | mvar π' y =>
        simp only [unifStep] at h
        split_ifs at h with hxy
        · obtain ⟨rfl, rfl⟩ := h
          subst hxy
          exact .mvarSame π π' x
        · obtain ⟨rfl, rfl⟩ := h
          exact .instL π x _ (by simpa [ntm.occursIn] using hxy)
      | atm a =>
        simp only [unifStep, ntm.occursIn, Bool.false_eq_true, if_false,
          StepResult.next.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .instL π x _ rfl
      | fapp f ts =>
        simp only [unifStep] at h
        split_ifs at h with hocc
        obtain ⟨rfl, rfl⟩ := h
        exact .instL π x _ (by simpa using hocc)
      | abs b t =>
        simp only [unifStep] at h
        split_ifs at h with hocc
        obtain ⟨rfl, rfl⟩ := h
        exact .instL π x _ (by simpa using hocc)
    | fapp f ss =>
      cases t with
      | fapp g ts =>
        simp only [unifStep] at h
        split_ifs at h with hfg
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨rfl, hlen⟩ := hfg
        exact .fapp f ss ts hlen
      | mvar π x =>
        simp only [unifStep] at h
        split_ifs at h with hocc
        obtain ⟨rfl, rfl⟩ := h
        exact .instR π x _ (by simpa using hocc)
      | atm _ | abs _ _ => simp [unifStep] at h
    | abs a s' =>
      cases t with
      | abs b t' =>
        simp only [unifStep] at h
        split_ifs at h with hab
        · obtain ⟨rfl, rfl⟩ := h
          subst hab
          exact .absSame a s' t'
        · obtain ⟨rfl, rfl⟩ := h
          exact .absDiff a b s' t' hab
      | mvar π x =>
        simp only [unifStep] at h
        split_ifs at h with hocc
        obtain ⟨rfl, rfl⟩ := h
        exact .instR π x _ (by simpa using hocc)
      | atm _ | fapp _ _ => simp [unifStep] at h

end Nominal
