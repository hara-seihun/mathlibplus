import MathlibPlus.Analysis.ThetaMellin

open scoped BigOperators

namespace MathlibPlus.Open.Analysis

/-- Claim 18845: every finite positive-index theta-shell cutoff has a positive
uncancelled first boundary jet. -/
noncomputable def finiteThetaShellFirstJet_claim18845 : Prop :=
  ∀ N : ℕ, 1 ≤ N →
    let phiN : ℝ → ℝ := fun u =>
      Finset.sum (Finset.range N) (fun m =>
        MathlibPlus.Analysis.ThetaMellin.thetaShell (m + 1) u)
    deriv phiN 0 =
        -(∑' m : ℕ,
          deriv
            (fun u : ℝ =>
              MathlibPlus.Analysis.ThetaMellin.thetaShell (N + m + 1) u) 0) ∧
      0 < deriv phiN 0

/-- Claim 18847: every finite-shell cosine transform is eventually negative on
its real axis. -/
noncomputable def finiteThetaShellEventuallyNegative_claim18847 : Prop :=
  ∀ N : ℕ, 1 ≤ N →
    let phiN : ℝ → ℝ := fun u =>
      Finset.sum (Finset.range N) (fun m =>
        MathlibPlus.Analysis.ThetaMellin.thetaShell (m + 1) u)
    let XN : ℂ → ℂ := fun z =>
      2 * ∫ u in Set.Ioi (0 : ℝ),
        (phiN u : ℂ) * Complex.cos (z * (u : ℂ))
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      ∃ r : ℝ, XN (t : ℂ) = (r : ℂ) ∧ r < 0

/-- Claim 18849: the finite-shell cosine transform has the stated order-one
imaginary-axis growth. -/
noncomputable def finiteThetaShellImaginaryGrowth_claim18849 : Prop :=
  ∀ N : ℕ, 1 ≤ N →
    let phiN : ℝ → ℝ := fun u =>
      Finset.sum (Finset.range N) (fun m =>
        MathlibPlus.Analysis.ThetaMellin.thetaShell (m + 1) u)
    let XN : ℂ → ℂ := fun z =>
      2 * ∫ u in Set.Ioi (0 : ℝ),
        (phiN u : ℂ) * Complex.cos (z * (u : ℂ))
    Asymptotics.IsBigO (Filter.atTop : Filter ℝ)
      (fun y : ℝ =>
        Real.log ‖XN (Complex.I * (y : ℂ))‖ -
          (y / 2) * Real.log y)
      (fun y : ℝ => y)

/-- Claim 18850: every finite-shell cosine transform is entire and has
infinitely many complex zeros. -/
noncomputable def finiteThetaShellInfiniteZeros_claim18850 : Prop :=
  ∀ N : ℕ, 1 ≤ N →
    let phiN : ℝ → ℝ := fun u =>
      Finset.sum (Finset.range N) (fun m =>
        MathlibPlus.Analysis.ThetaMellin.thetaShell (m + 1) u)
    let XN : ℂ → ℂ := fun z =>
      2 * ∫ u in Set.Ioi (0 : ℝ),
        (phiN u : ℂ) * Complex.cos (z * (u : ℂ))
    Differentiable ℂ XN ∧ Set.Infinite {z : ℂ | XN z = 0}

end MathlibPlus.Open.Analysis
