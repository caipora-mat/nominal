import NominalSets.FinitePerm.Basic
import Mathlib.GroupTheory.GroupAction.Hom

/-!
# Equivariant Functions

If `G` is a group and `X`, `X'` are `G`-sets (types equipped with a `MulAction` of `G`),
then a function `f : X → X'` is **equivariant** if it commutes with the group action:

  `f (g • x) = g • (f x)`

for all `g : G` and `x : X`.

Mathlib already provides this notion via `MulActionHom`:

* `MulActionHom (@id G) X Y` (notation: `X →[G] Y`) — the type of `G`-equivariant
  functions from `X` to `Y`.

This file introduces an abbreviation `Equivariant` specialized to finite permutations

## Main definitions

* `Equivariant α X Y` — abbreviation for `X →[FinitePerm 𝔸] Y`, the type of
  `FinitePerm α`-equivariant functions between types with a permutation action.

## References

* [A. M. Pitts, *Nominal Sets*][Pitts2013], Definition 1.3.
-/

open Equiv

/-- An **equivariant function** between two types with a `Perm α`-action is a function
that commutes with the action of every permutation. This is an abbreviation for
Mathlib's `MulActionHom (@id (Perm α)) X Y`, written `X →[Perm 𝔸] Y`. -/
abbrev Equivariant (α : Type*) [DecidableEq α]
    (X : Type*) [MulAction (FinitePerm α) X]
    (Y : Type*) [MulAction (FinitePerm α) Y] :=
  X →[FinitePerm α] Y

namespace Equivariant

variable {α : Type*} [DecidableEq α]
variable {X : Type*} [MulAction (Perm α) X]
variable {Y : Type*} [MulAction (Perm α) Y]

/-- Build an equivariant function from a plain function and a proof of equivariance. -/
def mk' (f : X → Y) (hf : ∀ (π : FinitePerm α) (x : X), f (π • x) = π • f x) :
    Equivariant α X Y :=
  ⟨f, hf⟩

end Equivariant
