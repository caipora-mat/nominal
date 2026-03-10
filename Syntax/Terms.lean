import NominalSets.Name
import NominalSets.FinitePerm
import NominalSets.Swap
import Syntax.LPerm
-- import Mathlib.Logic.Equiv.Basic

open NominalSets

section

variable {𝔸 : Type*} [Name 𝔸]
variable (a b : 𝔸)

end

inductive ntm (F X 𝔸 : Type*) [DecidableEq F] [DecidableEq X] [Name 𝔸] where
  | atm : 𝔸 → ntm F X 𝔸
  | mvar : LPerm 𝔸 → X → ntm F X 𝔸
  | fapp : F → List (ntm F X 𝔸) → ntm F X 𝔸
  | abs : 𝔸 → ntm F X 𝔸 → ntm F X 𝔸

-- #check (inferInstance : DecidableEq (ntm F X 𝔸))
-- #check instDecidableEqTm
