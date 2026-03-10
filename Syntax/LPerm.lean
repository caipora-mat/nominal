import NominalSets.Name

open NominalSets

def Swap (A : Type*) [Name A] := A × A

def LPerm (A : Type*) [Name A] := List (Swap A)

section

variable {𝔸 : Type*} [Name 𝔸]

def swapApply : Swap 𝔸 → 𝔸 → 𝔸
  | (a, b), c => if c = a then b
                   else if c = b then a
                     else c

def LPermApply : LPerm 𝔸 -> 𝔸 -> 𝔸
  | [], c => c
  | s :: sl, c => LPermApply sl (swapApply s c)

end
