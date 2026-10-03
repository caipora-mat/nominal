import Nominal.Syntax.Terms
import Nominal.Syntax.AlphaEquiv
import Nominal.Syntax.Substitution.Basic

namespace Nominal

open Core

variable {F X 𝔸 : Type*} [DecidableEq F] [DecidableEq X] [Name 𝔸]


/-- Computable list of atoms in a permutation. -/
def LPerm.atomsList : LPerm 𝔸 → List 𝔸
  | []           => []
  | (a, b) :: ps => a :: b :: LPerm.atomsList ps

/-- Computable difference list (may contain duplicates). -/
def dsList (π π' : LPerm 𝔸) : List 𝔸 :=
  (LPerm.atomsList π ++ LPerm.atomsList π').filter fun n =>
    LPermApply π n ≠ LPermApply π' n


/-- A constraint is either a freshness question `a #? t` or an alpha-equivalence question `s ≈α? t`. -/
inductive Constraint (F X 𝔸 : Type*) [DecidableEq F] [DecidableEq X] [Name 𝔸] where
  | fresh : 𝔸 → ntm F X 𝔸 → Constraint F X 𝔸
  | alpha : ntm F X 𝔸 → ntm F X 𝔸 → Constraint F X 𝔸

/-- A constraint problem is a list of constraints. -/
abbrev Problem (F X 𝔸 : Type*) [DecidableEq F] [DecidableEq X] [Name 𝔸] :=
  List (Constraint F X 𝔸)


/-- Apply a single substitution binding `[Y ↦ s]` to a constraint. -/
def Constraint.applyOne : Constraint F X 𝔸 → X → ntm F X 𝔸 → Constraint F X 𝔸
  | .fresh a t, Y, s => .fresh a (t.applyOne Y s)
  | .alpha u v, Y, s => .alpha (u.applyOne Y s) (v.applyOne Y s)

/-- Apply a single substitution binding `[Y ↦ s]` to a problem. -/
def Problem.applyOne (P : Problem F X 𝔸) (Y : X) (s : ntm F X 𝔸) : Problem F X 𝔸 :=
  P.map fun c => c.applyOne Y s


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


lemma LPerm.mem_atomsList_iff (n : 𝔸) (π : LPerm 𝔸) :
    n ∈ LPerm.atomsList π ↔ n ∈ LPerm.atoms π := by
  induction π with
  | nil => simp [LPerm.atomsList, LPerm.atoms]
  | cons p π ih =>
    obtain ⟨a, b⟩ := p
    simp [LPerm.atomsList, LPerm.atoms, ih]

lemma mem_dsList_iff_mem_ds (n : 𝔸) (π π' : LPerm 𝔸) :
    n ∈ dsList π π' ↔ n ∈ ds π π' := by
  simp only [dsList, ds, List.mem_filter, Finset.mem_filter, Finset.mem_union,
             List.mem_append, decide_not, Bool.not_eq_true', decide_eq_false_iff_not]
  rw [LPerm.mem_atomsList_iff, LPerm.mem_atomsList_iff]

end Nominal
