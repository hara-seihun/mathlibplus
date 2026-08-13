import MathlibPlus.Basic

namespace MathlibPlus.Analysis.Claim21435

/-!
The source uses endpoint derivative and logarithmic-derivative notation without
spelling out regularity.  `HasDerivAt` and nonvanishing endpoint hypotheses
make exactly those required conventions explicit.
-/

/-- The current quotient is the endpoint logarithmic derivative quotient. -/
theorem pressureAsSignedCurrentDeterminant_claim21435
    (d a b : ℝ) (J : ℝ → ℝ) (J'a J'b : ℝ)
    (ha : HasDerivAt J J'a a) (hb : HasDerivAt J J'b b)
    (ha0 : J a ≠ 0) (hb0 : J b ≠ 0) :
    d / 2 * (J'b / J b - J'a / J a) =
      d / 2 * (deriv (fun x => Real.log |J x|) b -
        deriv (fun x => Real.log |J x|) a) := by
  have hla : HasDerivAt (fun x => Real.log |J x|) (J'a / J a) a := by
    simpa [Real.log_abs] using ha.log ha0
  have hlb : HasDerivAt (fun x => Real.log |J x|) (J'b / J b) b := by
    simpa [Real.log_abs] using hb.log hb0
  rw [hla.deriv, hlb.deriv]

end MathlibPlus.Analysis.Claim21435
