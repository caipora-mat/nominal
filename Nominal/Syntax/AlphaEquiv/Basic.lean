import Nominal.Syntax.Terms
import Nominal.Syntax.Ds
import Nominal.Syntax.Fresh

namespace Nominal

open Core

variable {F X 𝔸 : Type*} [DecidableEq F] [DecidableEq X] [Name 𝔸]

mutual
  def alphaEquiv
    (Γ : Context 𝔸 X) : ntm F X 𝔸 → ntm F X 𝔸 → Bool
    -- (≈αa)
    | ntm.atm a, ntm.atm b => a = b
    -- (≈αX)
    | ntm.mvar π x, ntm.mvar π' y => x = y ∧ (∀ n ∈ ds π π', (n, x) ∈ Γ)
    -- (≈αtup)/(≈αf)
    | ntm.fapp f ss, ntm.fapp g ts => f = g ∧ alphaEquivList Γ ss ts
    -- (≈αabsa)/(≈αabsb)
    | ntm.abs a s, ntm.abs b t =>
        if a = b then alphaEquiv Γ s t
        else alphaEquiv Γ (ntm.permute [(b, a)] s) t ∧ fresh Γ b s
    | _, _ => false

  def alphaEquivList
    (Γ : Context 𝔸 X) : List (ntm F X 𝔸) → List (ntm F X 𝔸) → Bool
    | [], [] => true
    | s :: ss, t :: ts => alphaEquiv Γ s t ∧ alphaEquivList Γ ss ts
    | _,  _  => false
end

/-- Alpha-equivalence judgment: `Γ ⊢ s ≈α t` means `s` and `t` are alpha-equivalent under context `Γ`. -/
notation Γ " ⊢ " s " ≈α " t => alphaEquiv Γ s t

end Nominal
