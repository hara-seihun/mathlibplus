import Mathlib

namespace MathlibPlus.Analysis.Claim49588

/-- The rational arithmetic consequences of the displayed two-atom values in
claim 49588.  The source policy and mixture types are intentionally exposed as
hypotheses rather than reconstructed here. -/
theorem twoAtomSampledPolicyDefect_arithmetic_claim49588
    (F_h F_k E_F E_A A_g : ℚ)
    (hF_h : F_h = (212249 : ℚ) / 65536)
    (hF_k : F_k = (275743 : ℚ) / 65536)
    (hE_F : E_F = (6823715 : ℚ) / 2097152)
    (hE_A : E_A = (3331 : ℚ) / 1024)
    (hA_g : A_g = (212249 : ℚ) / 65536) :
    F_h = (212249 : ℚ) / 65536 ∧
      F_k = (275743 : ℚ) / 65536 ∧
      E_F = (6823715 : ℚ) / 2097152 ∧
      E_A = (3331 : ℚ) / 1024 ∧
      E_F - E_A = (1827 : ℚ) / 2097152 ∧
      0 < E_F - E_A ∧
      A_g = (212249 : ℚ) / 65536 ∧
      A_g - E_A = -(935 : ℚ) / 65536 ∧
      A_g - E_A < 0 := by
  subst F_h
  subst F_k
  subst E_F
  subst E_A
  subst A_g
  norm_num

end MathlibPlus.Analysis.Claim49588
