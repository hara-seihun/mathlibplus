import MathlibPlus.Open.ResearchFormalization.R1182.Claim31942

namespace MathlibPlus.Open.ResearchFormalization.R1182.Claim41709

open MathlibPlus.Open.ResearchFormalization.R1182.Claim31942

noncomputable def claim41709 : Prop :=
  letI : Fintype Axis := Fintype.ofFinite Axis
  letI : Fintype Outer := Fintype.ofFinite Outer
  letI : Fintype Nonidentity := Fintype.ofFinite Nonidentity
  letI : Fintype C4Axis := Fintype.ofFinite C4Axis
  voltageRankCertificate axisVoltageMatrix axisAugmentedMatrix 3 1 ∧
    voltageRankCertificate
      (fullVoltageMatrix
        (S := {h : Q12 | h.1 = 0 ∧ h ≠ (0, 0)}))
      (fullAugmentedMatrix
        (S := {h : Q12 | h.1 = 0 ∧ h ≠ (0, 0)})) 11 (-2) ∧
    voltageRankCertificate
      (fullVoltageMatrix (S := {h : Q12 | h.1 ≠ 0}))
      (fullAugmentedMatrix (S := {h : Q12 | h.1 ≠ 0})) 17 18 ∧
    voltageRankCertificate
      (fullVoltageMatrix
        (S := {h : Q12 | h.1 = 0 ∧ h ≠ (0, 0) ∨ h.1 ≠ 0}))
      (fullAugmentedMatrix
        (S := {h : Q12 | h.1 = 0 ∧ h ≠ (0, 0) ∨ h.1 ≠ 0})) 20 12

end MathlibPlus.Open.ResearchFormalization.R1182.Claim41709
