import NominalSets
import Mathlib.Data.Finset.Basic
import NominalSets.Experiments
import Mathlib.Data.Finset.Sort

open NominalSets

-- Let's try to do lambda terms as nominal sets.

inductive tm (𝔸 : Type) [Name 𝔸] : Type where
  | var   : 𝔸 -> tm 𝔸
  | app   : tm 𝔸 -> tm 𝔸 -> tm 𝔸
  | lam  : 𝔸 -> tm 𝔸 -> tm 𝔸

open tm

-- this is syntactic equality, and i wanna use that as DecEq for this type (no α-equivalence)
def lam_eq_dec
    {𝔸 : Type}
    [Name 𝔸]
    (s : tm 𝔸)
    (t : tm 𝔸)
  : Bool :=
  match s,t with
  | var x, var y => decide (x = y)
  | app s₁ s₂, app t₁ t₂ =>
    lam_eq_dec s₁ t₁ && lam_eq_dec s₂ t₂
  | lam x s, lam y t => x = y && lam_eq_dec s t
  | _ , _ => false

lemma lam_eq_dec_correct
  {𝔸 : Type} [Name 𝔸] :
  ∀ s t : tm 𝔸,
  lam_eq_dec s t = true ↔ s = t
    | var x, var y => by
        simp [lam_eq_dec]
    | app s₁ s₂, app t₁ t₂ => by
        simp [lam_eq_dec,
              lam_eq_dec_correct s₁ t₁,
              lam_eq_dec_correct s₂ t₂]
    | lam x s, lam y t => by
        simp [lam_eq_dec,
              lam_eq_dec_correct s t]
    | var _, app _ _
    | var _, lam _ _
    | app _ _, var _
    | app _ _, lam _ _
    | lam _ _, var _
    | lam _ _, app _ _ => by
        simp [lam_eq_dec]

instance {𝔸 : Type} [Name 𝔸] :
  DecidableEq (tm 𝔸) :=
  fun s t =>
    if h : lam_eq_dec s t = true then
      isTrue ((lam_eq_dec_correct s t).1 h)
    else
      isFalse (by
        intro hst
        have : lam_eq_dec s t = true :=
          (lam_eq_dec_correct s t).2 hst
        contradiction)

-- finished equality, let's go back to free names

def free_names
  {𝔸 : Type}
  [Name 𝔸]
  (s : tm 𝔸)
  : Finset 𝔸 :=
  match s with
  | var x => { x }
  | app s t => free_names s ∪ free_names t
  | lam a s => free_names s \ {a}

-- Example to compute with free_names

def s := var 1
def finset := free_names s

#eval (finset)

-- Todo: define the action of finite permutations on the names of a lambda term


-- Todo: then use this to show that lam 𝔸 is nominal
