import NominalSets
import Mathlib.Data.Finset.Basic
import NominalSets.Experiments
import Mathlib.Data.Finset.Sort

open NominalSets

-- Let's try to do lambda terms as nominal sets.

variable {𝔸 : Type*} [Name 𝔸]

inductive tm where
  | var : 𝔸 → tm
  | app : tm → tm → tm
  | lam : 𝔸 → tm → tm
deriving DecidableEq

#check (inferInstance : DecidableEq tm)
#check instDecidableEqTm

#eval (tm.var 1 = tm.var 2) -- false
#eval (tm.var 0 = tm.var 0) -- true
#eval (tm.var 0 == tm.var 0) -- true
#eval (tm.var 1 == tm.var 2) -- false

-- https://leanprover-community.github.io/mathlib4_docs/tactics.html#Lean.Parser.Tactic.decide
example : tm.var 1 == tm.var 1 := by simp
example : tm.var 1 == tm.var 1 := by decide

-- -- this is syntactic equality, and i wanna use that as DecEq for this type (no α-equivalence)
-- def lam_eq_dec
--     {𝔸 : Type}
--     [Name 𝔸]
--     (s : tm 𝔸)
--     (t : tm 𝔸)
--   : Bool :=
--   match s,t with
--   | var x, var y => decide (x = y)
--   | app s₁ s₂, app t₁ t₂ =>
--     lam_eq_dec s₁ t₁ && lam_eq_dec s₂ t₂
--   | lam x s, lam y t => x = y && lam_eq_dec s t
--   | _ , _ => false

-- lemma lam_eq_dec_correct
--   {𝔸 : Type} [Name 𝔸] :
--   ∀ s t : tm 𝔸,
--   lam_eq_dec s t = true ↔ s = t
--     | var x, var y => by
--         simp [lam_eq_dec]
--     | app s₁ s₂, app t₁ t₂ => by
--         simp [lam_eq_dec,
--               lam_eq_dec_correct s₁ t₁,
--               lam_eq_dec_correct s₂ t₂]
--     | lam x s, lam y t => by
--         simp [lam_eq_dec,
--               lam_eq_dec_correct s t]
--     | var _, app _ _
--     | var _, lam _ _
--     | app _ _, var _
--     | app _ _, lam _ _
--     | lam _ _, var _
--     | lam _ _, app _ _ => by
--         simp [lam_eq_dec]

-- -- finished equality, let's go back to free names

def free_names : @tm 𝔸 → Finset 𝔸
  | .var x => { x }
  | .app s t => free_names s ∪ free_names t
  | .lam a s => free_names s \ {a}

def names : @tm 𝔸 → Finset 𝔸
  | .var x => { x }
  | .app s t => free_names s ∪ free_names t
  | .lam a s => free_names s ∪ {a}

-- -- Example to compute with free_names

-- def s := var 1
-- def finset := free_names s

-- #eval (finset)

-- Todo: define the action of finite permutations on the names of a lambda term


-- Todo: then use this to show that lam 𝔸 is nominal
