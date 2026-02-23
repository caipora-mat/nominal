import Mathlib.Data.Finite.Defs

/-!
# Names (Atoms)

The type of **names** (also called *atoms*) is parametric: any type `𝔸` satisfying
`Name 𝔸` can serve as the set of atoms. The only requirements are:

- `DecidableEq 𝔸` — names can be compared for equality;
- `Infinite 𝔸` — there are infinitely many names.

The concrete identity of names is irrelevant; only these two structural properties
matter. The canonical example is `ℕ`, but the library is parametric in the atom type.
-/

/-- A **name** type (also called *atoms*) is any type with decidable equality
and infinitely many inhabitants. -/
class Name (𝔸 : Type*) extends Infinite 𝔸 where
  [dec : DecidableEq 𝔸]

attribute [instance] Name.dec
