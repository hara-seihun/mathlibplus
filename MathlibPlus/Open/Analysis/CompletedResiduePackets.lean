import Mathlib

noncomputable section

namespace MathlibPlus.Open.Analysis

/-- The Chebyshev `psi` function, written as the finite prime-power sum used here. -/
def chebyshevPsi (n : ℕ) : ℝ :=
  ∑ q ∈ (Finset.range (n + 1)).filter Nat.Prime,
    ∑ _j ∈ (Finset.range (n + 1)).filter (fun j => 1 ≤ j ∧ q ^ j ≤ n),
      Real.log (q : ℝ)

/-- The finite prime-divisor factor in the generalized-Jordan representation. -/
def generalizedJordanFactor (p n : ℕ) (w : ℂ) : ℂ :=
  ∏ q ∈ (Nat.primeFactors n).filter (fun q => q ≠ p),
    (1 - (q : ℂ) ^ (-w))

/-- The finite generalized-Jordan sum `A_{p,w}(x)`. -/
def generalizedJordanSum (p x : ℕ) (w : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 x, generalizedJordanFactor p n w

/-- The local density factor `c_{p,w}`. -/
def completedResidueCoefficient (p : ℕ) (w : ℂ) : ℂ :=
  1 / (riemannZeta (1 + w) * (1 - (p : ℂ) ^ (-1 - w)))

/-- The completed residue sum in shifted parameter `w`, via its exact
    generalized-Jordan representation. -/
def completedResidueShift (p a : ℕ) (w : ℂ) : ℂ :=
  completedResidueCoefficient p w * ((p ^ a : ℕ) : ℂ) -
    generalizedJordanSum p (p ^ a) w

/-- `F_{p^a}(z)`, with the shifted representation evaluated at `w = z - 1`. -/
def completedResidueSum (p a : ℕ) (z : ℂ) : ℂ :=
  completedResidueShift p a (z - 1)

/-- The outer Möbius completion `C_p(w)`. -/
def outerMobiusCompletion (p : ℕ) (w : ℂ) : ℂ :=
  1 / (riemannZeta w * (1 - (p : ℂ) ^ (-w))) - 1

/-- The completed packet transform `T_{p,a}(w)`. -/
def completedPacketTransform (p a : ℕ) (w : ℂ) : ℂ :=
  outerMobiusCompletion p w - 2 * completedResidueShift p a w

/-- The regular packet `B_{p,a}(w)`. -/
def regularPacket (p a : ℕ) (w : ℂ) : ℂ :=
  completedPacketTransform p a w -
    (p : ℂ) ^ (-w) * completedPacketTransform p (a - 1) w

/-- Claim 13948: the first-depth completed derivative difference. -/
def firstDepthCompletedDerivativeDifference : Prop :=
  ∀ ⦃p : ℕ⦄, Nat.Prime p →
    deriv (completedResidueSum p 1) 1 - deriv (completedResidueSum p 0) 1 =
      (p : ℂ) - Complex.ofReal (chebyshevPsi p) +
        Complex.ofReal (Real.log (p : ℝ))

/-- Claim 13949: the removable first-packet coefficient and its punctured
    first-order limit. -/
def removableFirstPacketCoefficient : Prop :=
  ∀ ⦃p : ℕ⦄, Nat.Prime p →
    Filter.Tendsto (fun w : ℂ => regularPacket p 1 w)
        (nhdsWithin 0 {0}ᶜ) (nhds 0) ∧
      Filter.Tendsto (fun w : ℂ => regularPacket p 1 w / w)
        (nhdsWithin 0 {0}ᶜ)
        (nhds (Complex.ofReal
          (2 * (chebyshevPsi p - (p : ℝ)) +
            2 * Real.log (2 * Real.pi) - Real.log (p : ℝ))))

/-- Claim 13954: the all-depth completed derivative increment. -/
def completedDerivativeIncrement : Prop :=
  ∀ ⦃p : ℕ⦄, Nat.Prime p → ∀ ⦃a : ℕ⦄, 1 ≤ a →
    deriv (completedResidueSum p a) 1 -
        deriv (completedResidueSum p (a - 1)) 1 =
      ((p ^ a : ℕ) : ℂ) - Complex.ofReal (chebyshevPsi (p ^ a)) +
        (a : ℂ) * Complex.ofReal (Real.log (p : ℝ))

end MathlibPlus.Open.Analysis
