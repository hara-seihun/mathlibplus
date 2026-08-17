import MathlibPlus.Algebra.Claim42889
import MathlibPlus.Open.ResearchFormalizationBatch.Shell

namespace MathlibPlus.Open.ResearchFormalization.BatchR2625Tail

open scoped BigOperators
open MathlibPlus.Algebra.Claim42889
open MathlibPlus.Open.ResearchFormalizationBatch.Shell

noncomputable section

abbrev Vec4 := Fin 4 → ℝ

/-- The divided moment vector of one positive Gaussian shell. -/
def shellVector (n : ℕ) : Vec4 :=
  fun k => dividedShellMoment n k.val

/-- The vector obtained by summing the shells whose labels are divisible by d.
This is the concrete carrier denoted M^(d) in the retained R-2625 record. -/
def divisibleShellVector (d : ℕ) : Vec4 :=
  fun k =>
    ∑' n : ℕ,
      if 1 ≤ n ∧ d ∣ n then shellVector n k else 0

/-- The determinant evaluated on the even divisible-shell vector. -/
def evenShellDeterminant (r : ℕ) : ℝ :=
  determinantPieces (divisibleShellVector (2 * r))

/-- The absolute determinant-tail term occurring at the even shell 2r. -/
def evenShellTailTerm (r : ℕ) : ℝ :=
  |evenShellDeterminant r|

/-- The componentwise Gaussian majorant used for the even-shell tail. -/
def evenShellMajorant (r : ℕ) : ℝ :=
  Real.exp (-4 * Real.pi * (r : ℝ) ^ 2) /
    (Real.pi * (r : ℝ) ^ 2)

/-- Claim 42897: the successive determinant-tail ratio and the resulting
geometric Möbius-correction bound, with the displayed decimal threshold. -/
def geometricMobiusCorrectionBound_claim42897 : Prop :=
  (∀ r : ℕ, 2 ≤ r →
    evenShellTailTerm (r + 1) / evenShellTailTerm r ≤
      Real.exp (-40 * Real.pi)) ∧
  (∑' r : ℕ, if 2 ≤ r then evenShellTailTerm r else 0) <
    3 * evenShellMajorant 2 ^ 2 /
      (1 - Real.exp (-40 * Real.pi)) ∧
  3 * evenShellMajorant 2 ^ 2 /
      (1 - Real.exp (-40 * Real.pi)) <
    (4.156 : ℝ) * 10 ^ (-46 : ℤ)

end
end MathlibPlus.Open.ResearchFormalization.BatchR2625Tail
