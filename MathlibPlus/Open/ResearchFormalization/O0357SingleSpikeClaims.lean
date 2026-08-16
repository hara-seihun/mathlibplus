import MathlibPlus.Open.Research.PoissonTuran

open Filter
open scoped BigOperators Topology

namespace MathlibPlus.Open.ResearchFormalization.O0357SingleSpike

noncomputable section

/-- The positive-parameter hypothesis fixed by the moving single-spike packet. -/
def spikeParameter (x₀ c : ℝ) : Prop :=
  0 < x₀ ∧ Real.rpow x₀ (-(1 / 2 : ℝ)) < c

/-- The exact single-spike polynomial `A_N(z)=(cz)^N/sqrt(N!)`. -/
noncomputable def spikePolynomial
    (c : ℝ) (N : ℕ+) (z : ℂ) : ℂ :=
  ((c : ℂ) * z) ^ (N : ℕ) /
    (Real.sqrt (Nat.factorial (N : ℕ) : ℝ) : ℂ)

/-- Its asserted disk supremum value. -/
noncomputable def spikeSupremum
    (c R : ℝ) (N : ℕ+) : ℝ :=
  (c * R) ^ (N : ℕ) /
    Real.sqrt (Nat.factorial (N : ℕ) : ℝ)

/-- The EGF coefficient sequence of the single spike. -/
noncomputable def spikeCoefficients
    (c : ℝ) (N : ℕ+) (n : ℕ) : ℝ :=
  if n = (N : ℕ) then
    Real.sqrt (Nat.factorial (N : ℕ) : ℝ) * c ^ (N : ℕ)
  else 0

/-- The exact Poisson Turan scalar of the single-spike coefficients. -/
noncomputable def spikeTuranScalar
    (x₀ c : ℝ) (N : ℕ+) : ℝ :=
  MathlibPlus.Open.Research.PoissonTuran.poissonTuranFunctional
    (spikeCoefficients c N) x₀

/-- The weighted Poisson/Fock square energy of a coefficient sequence. -/
noncomputable def poissonFockEnergy
    (x : ℝ) (u : ℕ → ℝ) : ℝ :=
  Real.exp (-x) *
    ∑' n : ℕ,
      ‖u n‖ ^ 2 * x ^ n / (Nat.factorial n : ℝ)

/-- Claim 15685: the exact disk suprema of the spikes tend to zero. -/
def claim15685 : Prop :=
  ∀ (x₀ c : ℝ),
    spikeParameter x₀ c →
      ∀ R : ℝ,
        0 < R →
          (∀ N : ℕ+, 
            sSup
                ((fun z : ℂ => ‖spikePolynomial c N z‖) ''
                  {z : ℂ | ‖z‖ ≤ R}) =
              spikeSupremum c R N) ∧
            Tendsto
              (fun N : ℕ+ => spikeSupremum c R N)
              atTop (𝓝 (0 : ℝ))

/-- Claim 15686: every fixed complex derivative order also disappears
uniformly on each fixed disk. -/
def claim15686 : Prop :=
  ∀ (x₀ c : ℝ),
    spikeParameter x₀ c →
      ∀ (k : ℕ) (R : ℝ),
        0 < R →
          Tendsto
            (fun N : ℕ+ =>
              sSup
                ((fun z : ℂ =>
                    ‖iteratedDeriv k (spikePolynomial c N) z‖) ''
                  {z : ℂ | ‖z‖ ≤ R}))
            atTop (𝓝 (0 : ℝ))

/-- Claim 15688: the exact single-spike Turan value and its negative
infinite limit. -/
def claim15688 : Prop :=
  ∀ (x₀ c : ℝ),
    spikeParameter x₀ c →
      (∀ N : ℕ+,
        spikeTuranScalar x₀ c N =
          -Real.exp (-x₀) * ((N : ℝ) / x₀) *
            (c ^ 2 * x₀) ^ (N : ℕ)) ∧
      Tendsto
        (fun N : ℕ+ => spikeTuranScalar x₀ c N)
        atTop atBot

/-- Claim 15689: the corresponding weighted square energy diverges. -/
def claim15689 : Prop :=
  ∀ (x₀ c : ℝ),
    spikeParameter x₀ c →
      (∀ N : ℕ+,
        poissonFockEnergy x₀ (spikeCoefficients c N) =
          Real.exp (-x₀) * (c ^ 2 * x₀) ^ (N : ℕ)) ∧
      Tendsto
        (fun N : ℕ+ =>
          poissonFockEnergy x₀ (spikeCoefficients c N))
        atTop atTop

end

end MathlibPlus.Open.ResearchFormalization.O0357SingleSpike
