import Nominal

/-! The expected diagnostic is evidence about registration with an atom outParam,
not a mathematical obstruction to treating Prop as a discrete nominal carrier. -/
open Nominal.Core Nominal.Set
universe u

/--
error: cannot find synthesization order for instance @badGenericPropInstance with type
  {α : Type u} → [inst : Name α] → Nominal α Prop
all remaining arguments have metavariables:
  Name ?α
-/
#guard_msgs in
local instance badGenericPropInstance {α : Type u} [Name α] : Nominal α Prop where
  smul _ P := P
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  finSupp _ := ⟨∅, fun _ _ => rfl⟩
