import Mathlib
import MathlibPlus.Open.ResearchFormalization.Claim14975ExactLeakageComplement
import MathlibPlus.Open.ResearchFormalization.O0193LocalLogFrequency

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace MathlibPlus.Open.ResearchFormalization.Claim14976

noncomputable section

abbrev SourceFunction :=
  MathlibPlus.Open.ResearchFormalization.Claim14975.SourceFunction
abbrev FourierHilbert :=
  MathlibPlus.Open.ResearchFormalization.Claim14975.FourierHilbert

/-- The symmetric translated source bump used by the escaping-packet family. -/
def modulatedPair (b : ℝ → ℝ) (x₀ ω : ℝ) : SourceFunction :=
  fun x =>
    (MathlibPlus.Open.ResearchFormalization.O0193LocalLogFrequency.symmetricPair
      b x₀ x : ℂ) * (Real.cos (ω * x) : ℂ)

/-- A finite linear combination of the actual symmetric-pair modulations. -/
def modulationCombination {m : ℕ} (b : ℝ → ℝ) (x₀ : ℝ)
    (omega : ℕ → Fin m → ℝ) (a : ℕ → Fin m → ℝ) (n : ℕ) : SourceFunction :=
  fun x =>
    ∑ j : Fin m, (a n j : ℂ) * modulatedPair b x₀ (omega n j) x

/-- One fixed absolute-width pair of Fourier packets around the two carriers. -/
def packetSet (omega width : ℝ) : Set ℝ :=
  {xi | |xi - omega| ≤ width / 2 ∨ |xi + omega| ≤ width / 2}

/-- The union of all packet neighborhoods at one stage of the family. -/
def packetUnion {m : ℕ} (omega : Fin m → ℝ)
    (width : Fin m → ℝ) : Set ℝ :=
  {xi | ∃ j : Fin m, xi ∈ packetSet (omega j) (width j)}

/-- Exterior Fourier mass outside the finite union of packets. -/
noncomputable def packetMassError (lambda : ℝ) (f : SourceFunction)
    (hf : MemLp f 2 (volume : Measure ℝ))
    {m : ℕ} (omega : Fin m → ℝ) (width : Fin m → ℝ) : ℝ :=
  Real.sqrt
    (∫ xi in (packetUnion omega width)ᶜ,
      ‖MathlibPlus.Open.ResearchFormalization.Claim14975.leakageOf
        lambda f hf xi‖ ^ 2)

/-- The logarithmic width of a fixed-width packet in the coordinate
`y = log (xi / lambda)`. -/
noncomputable def logarithmicPacketWidth
    (lambda omega width : ℝ) : ℝ :=
  Real.log ((omega + width / 2) / lambda) -
    Real.log ((omega - width / 2) / lambda)

/-- Explicit `o(1)` modulo `2*pi` convergence for one prime phase. -/
def phaseReturn (theta : ℕ → ℝ) (p : ℕ)
    (tau : ℕ → ℝ) : Prop :=
  ∃ k : ℕ → ℤ,
    Tendsto
      (fun n : ℕ =>
        tau n * Real.log (p : ℝ) - theta p -
          2 * Real.pi * (k n : ℝ))
      atTop (𝓝 0)

/-- All carrier sums and pairwise differences escape to infinity. -/
def remoteCarrierFamily {m : ℕ}
    (omega : ℕ → Fin m → ℝ) : Prop :=
  (∀ j : Fin m,
    Tendsto (fun n : ℕ => |omega n j|) atTop atTop) ∧
    (∀ j k : Fin m, j ≠ k →
      Tendsto (fun n : ℕ => |omega n j + omega n k|) atTop atTop ∧
        Tendsto (fun n : ℕ => |omega n j - omega n k|) atTop atTop)

/-- The local logarithmic frequency of the actual positive packet generated
by the symmetric pair, rather than an independently chosen witness. -/
noncomputable def localPacketFrequency
    (lambda x₀ omega : ℝ) : ℝ :=
  MathlibPlus.Open.ResearchFormalization.O0193LocalLogFrequency.localLogFrequency
    lambda x₀ omega

/-- Claim 14976: every finite exact-source flag admits a normalized even
compactly supported family of exact leakage-orthogonal symmetric-pair
modulations.  Its exterior mass is concentrated in one finite union of
fixed-width remote packets, whose relative and logarithmic widths vanish;
the phase variable is the local frequency of those same packets. -/
def claim14976 : Prop :=
  ∀ (lambda epsilon : ℝ)
    (S : Submodule ℝ SourceFunction)
    (primes : Finset ℕ) (theta : ℕ → ℝ),
    0 < lambda →
      0 < epsilon →
        Module.Finite ℝ S →
          (∀ s : S,
            MathlibPlus.Open.ResearchFormalization.Claim14975.exactSource
              lambda (s : SourceFunction)) →
            (∀ p ∈ primes, Nat.Prime p) →
              ∃ (m : ℕ) (b : ℝ → ℝ) (x₀ W : ℝ)
                (f : ℕ → SourceFunction)
                (hf : ∀ n : ℕ,
                  MemLp (f n) 2 (volume : Measure ℝ))
                (omega : ℕ → Fin m → ℝ)
                (width : Fin m → ℝ)
                (a : ℕ → Fin m → ℝ),
                0 < m ∧
                  MathlibPlus.Open.ResearchFormalization.O0193LocalLogFrequency.symmetricPairBump lambda x₀ b ∧
                    0 < W ∧
                    (∀ n : ℕ,
                      f n = modulationCombination b x₀ omega a n) ∧
                    (∀ n : ℕ,
                      ∑ j : Fin m, (a n j) ^ 2 = 1) ∧
                    (∀ n : ℕ,
                      MathlibPlus.Open.ResearchFormalization.Claim14975.exactSource
                          lambda (f n) ∧
                        ‖MathlibPlus.Open.ResearchFormalization.Claim14975.sourceToHilbert (f n) (hf n)‖ = 1 ∧
                        MathlibPlus.Open.ResearchFormalization.Claim14975.l2OrthogonalTo
                          (MathlibPlus.Open.ResearchFormalization.Claim14975.leakageImage lambda S)
                          (MathlibPlus.Open.ResearchFormalization.Claim14975.leakageOf lambda (f n) (hf n))) ∧
                    (∀ j : Fin m,
                      ∀ n : ℕ,
                        0 < width j ∧
                          width j ≤ W ∧
                          0 < omega n j ∧
                          lambda < omega n j - width j / 2) ∧
                    remoteCarrierFamily omega ∧
                    (∀ j : Fin m,
                      Tendsto (fun n : ℕ => omega n j) atTop atTop) ∧
                    (∀ j : Fin m,
                      Tendsto (fun n : ℕ => width j / omega n j)
                        atTop (𝓝 0)) ∧
                    (∀ j : Fin m,
                      Tendsto
                        (fun n : ℕ =>
                          logarithmicPacketWidth lambda (omega n j) (width j))
                        atTop (𝓝 0)) ∧
                    (∀ n : ℕ,
                      packetMassError lambda (f n) (hf n)
                        (fun j : Fin m => omega n j) width ≤ epsilon) ∧
                    (∀ j : Fin m,
                      Tendsto
                        (fun n : ℕ =>
                          (localPacketFrequency lambda x₀ (omega n j) -
                            x₀ * omega n j) / omega n j)
                        atTop (𝓝 0)) ∧
                    (∀ j : Fin m, ∀ p ∈ primes,
                      phaseReturn theta p
                        (fun n : ℕ =>
                          localPacketFrequency lambda x₀ (omega n j)))

end

end MathlibPlus.Open.ResearchFormalization.Claim14976
