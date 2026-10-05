import Nominal

/-!
Research probe, 2026-10-05, Lean 4.34.1.
Run: `lake env lean docs/research/probes/BackendPositivity.lean`.
All three failures are intentional and checked by `#guard_msgs`.
The discrete structure below isolates the kernel obstruction; it is not a
proposed action on syntax and does not repair the construction.
-/

open Nominal.Core Nominal.Set

universe u

namespace BackendPositivity

/--
error: failed to synthesize instance of type class
  Nominal α (Direct α)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
inductive Direct (α : Type u) [Name α] where
  | var : α → Direct α
  | bind : NameAbs α (Direct α) → Direct α

def Collapsed (X : Type) : Type := Quot (fun (_ _ : X) => True)

/--
error: (kernel) arg #1 of 'BackendPositivity.UnderQuot.mk' contains a non valid occurrence of the datatypes being declared
-/
#guard_msgs in
inductive UnderQuot where
  | mk : Collapsed UnderQuot → UnderQuot

@[instance_reducible]
def discreteNominal (α : Type u) [Name α] (X : Type u) : Nominal α X where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  finSupp _ := ⟨∅, fun _ _ => rfl⟩

/--
error: (kernel) arg #3 of 'BackendPositivity.DirectDiscrete.bind' contains a non valid occurrence of the datatypes being declared
-/
#guard_msgs in
inductive DirectDiscrete (α : Type u) [Name α] where
  | var : α → DirectDiscrete α
  | bind : @NameAbs α _ (DirectDiscrete α)
      (discreteNominal α (DirectDiscrete α)) → DirectDiscrete α

#print axioms discreteNominal

end BackendPositivity
