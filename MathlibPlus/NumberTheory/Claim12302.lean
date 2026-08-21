-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is a root of the Unverified library rather than of MathlibPlus and no build here depends on it. See unverified.txt.
import Mathlib

namespace MathlibPlus.NumberTheory.Claim12302

/-- The affine point count and the resulting Frobenius arithmetic for
`y^2 = x^3 + 2*x` over `ZMod 5`.  The projective point at infinity is the
additional `+ 1` in the count; the trace convention is `p + 1 - #E`. -/
theorem ellipticCurveE2_F5_arithmetic :
    let E : Finset (ZMod 5 × ZMod 5) :=
      Finset.univ.filter (fun p : ZMod 5 × ZMod 5 =>
        p.2 ^ 2 = p.1 ^ 3 + 2 * p.1)
    let cardE : ℕ := E.card + 1
    let trace : ℤ := (5 : ℤ) + 1 - cardE
    cardE = 2 ∧
      trace = 4 ∧
      ((Polynomial.X : Polynomial ℤ) ^ 2 - Polynomial.C trace * Polynomial.X +
          Polynomial.C 5) =
        (Polynomial.X : Polynomial ℤ) ^ 2 - Polynomial.C 4 * Polynomial.X +
          Polynomial.C 5 ∧
      (1 - Polynomial.C trace * Polynomial.X +
          Polynomial.C 5 * Polynomial.X ^ 2 : Polynomial ℤ) =
        1 - Polynomial.C 4 * Polynomial.X + Polynomial.C 5 * Polynomial.X ^ 2 := by
  dsimp
  have hcard :
      (Finset.univ.filter (fun p : ZMod 5 × ZMod 5 =>
        p.2 ^ 2 = p.1 ^ 3 + 2 * p.1)).card + 1 = 2 := by
    native_decide
  have hcardNat :
      (Finset.univ.filter (fun p : ZMod 5 × ZMod 5 =>
        p.2 ^ 2 = p.1 ^ 3 + 2 * p.1)).card = 1 := by
    omega
  have hcardInt :
      ((Finset.univ.filter (fun p : ZMod 5 × ZMod 5 =>
        p.2 ^ 2 = p.1 ^ 3 + 2 * p.1)).card : ℤ) = 1 := by
    exact_mod_cast hcardNat
  refine ⟨hcard, ?_, ?_, ?_⟩ <;> norm_num [hcardInt]

end MathlibPlus.NumberTheory.Claim12302
