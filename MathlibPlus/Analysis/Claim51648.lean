import Mathlib

namespace MathlibPlus.Analysis.Claim51648

/-- A finite rational law on the support indices appearing in claim 51648.
The source packet does not need any further structure on the law for the exact
functional values below, so the carrier is kept explicit as a function. -/
abbrev Law := Fin 236 → ℚ

def atom (i : Fin 236) : Law := fun j => if j = i then 1 else 0

def mix (t : ℚ) (nu mu : Law) : Law :=
  fun j => t * nu j + (1 - t) * mu j

def nu0 : Law := fun j =>
  (1 / 4 : ℚ) * atom 96 j +
    (5 / 8 : ℚ) * atom 22 j +
    (1 / 8 : ℚ) * atom 126 j

def nu1 : Law := fun j =>
  (5 / 24 : ℚ) * atom 176 j +
    (7 / 12 : ℚ) * atom 25 j +
    (5 / 24 : ℚ) * atom 207 j

def defect (B : Law → ℚ) (h : Fin 236) (nu : Law) (t : ℚ) : ℚ :=
  B (mix t (atom h) nu) - (1 - t) ^ 2 * B nu

def d0 : ℚ := -231637 / 262144

def d1 : ℚ := -1487675 / 2359296

def dm : ℚ := -76292059 / 95551488

def jensenGap (B : Law → ℚ) : ℚ :=
  defect B 235 (mix (2 / 3) nu0 nu1) (7 / 8) -
    ((2 / 3 : ℚ) * defect B 235 nu0 (7 / 8) +
      (1 / 3 : ℚ) * defect B 235 nu1 (7 / 8))

/-- The exact three defect evaluations asserted in claim 51648. -/
def exactDefectData_claim51648 (B : Law → ℚ) : Prop :=
  defect B 235 nu0 (7 / 8) = d0 ∧
    defect B 235 nu1 (7 / 8) = d1 ∧
    defect B 235 (mix (2 / 3) nu0 nu1) (7 / 8) = dm

/-- The three exact defect values yield the stated positive Jensen gap. -/
theorem jensenGap_claim51648
    {B : Law → ℚ} (hB : exactDefectData_claim51648 B) :
    jensenGap B = 158689 / 191102976 := by
  rcases hB with ⟨h0, h1, hm⟩
  unfold jensenGap
  rw [h0, h1, hm]
  norm_num [d0, d1, dm]

/-- Each of the three exact defects in claim 51648 is negative. -/
theorem defects_negative_claim51648
    {B : Law → ℚ} (hB : exactDefectData_claim51648 B) :
    defect B 235 nu0 (7 / 8) < 0 ∧
      defect B 235 nu1 (7 / 8) < 0 ∧
      defect B 235 (mix (2 / 3) nu0 nu1) (7 / 8) < 0 := by
  rcases hB with ⟨h0, h1, hm⟩
  constructor
  · rw [h0]
    norm_num [d0]
  constructor
  · rw [h1]
    norm_num [d1]
  · rw [hm]
    norm_num [dm]

end MathlibPlus.Analysis.Claim51648
