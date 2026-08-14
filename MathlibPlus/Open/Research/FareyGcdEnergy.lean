import Mathlib

noncomputable section

open scoped BigOperators

namespace MathlibPlus.Open.Research.FareyGcdEnergy

private abbrev IccNat (N : ℕ) : Finset ℕ := Finset.Icc 1 N

def mobius (n : ℕ) : ℤ := ArithmeticFunction.moebius n

def mertens (N : ℕ) : ℤ :=
  ∑ d ∈ IccNat N, mobius d

def fareyDenominatorCount (N : ℕ) : ℕ :=
  ∑ q ∈ IccNat N, Nat.totient q

def reducedResidues (q : ℕ) : Finset ℕ :=
  (Finset.Icc 1 q).filter (fun a => Nat.Coprime a q)

def ramanujanSum (q : ℕ) (k : ℤ) : ℂ :=
  ∑ a ∈ reducedResidues q,
    Complex.exp
      (2 * (Real.pi : ℂ) * Complex.I *
        ((a : ℂ) * (k : ℂ) / (q : ℂ)))

def summedRamanujanLayer (N : ℕ) (k : ℤ) : ℂ :=
  ∑ q ∈ IccNat N, ramanujanSum q k

def fareyResidueSum (N : ℕ) (k : ℤ) : ℂ :=
  ∑ q ∈ IccNat N, ∑ a ∈ reducedResidues q,
    Complex.exp
      (2 * (Real.pi : ℂ) * Complex.I *
        ((a : ℂ) * (k : ℂ) / (q : ℂ)))

def fareyFourierCoefficient (N : ℕ) (k : ℤ) : ℂ :=
  fareyResidueSum N k / (fareyDenominatorCount N : ℂ)

def gcdKernel (d e : ℕ) : ℝ :=
  (Nat.gcd d e : ℝ) ^ 2 / ((d : ℝ) * (e : ℝ))

def levelWeight (N d : ℕ) : ℤ :=
  mertens (N / d)

def gcdEnergy (N : ℕ) : ℝ :=
  ∑ d ∈ IccNat N, ∑ e ∈ IccNat N,
    (levelWeight N d : ℝ) * (levelWeight N e : ℝ) * gcdKernel d e

def periodicEnergy (N : ℕ) : ℝ :=
  ∑' k : ℤ,
    if k = 0 then 0
    else
      Complex.normSq (fareyFourierCoefficient N k) /
        (4 * (Real.pi : ℝ) ^ 2 * (k : ℝ) ^ 2)

def claim42703 : Prop :=
  ∀ (N : ℕ), 1 ≤ N →
    ∀ k : ℤ, k ≠ 0 →
      summedRamanujanLayer N k =
          ∑ d ∈ (IccNat N).filter (fun d => d ∣ k.natAbs),
            (d : ℂ) * (mertens (N / d) : ℂ) ∧
        fareyFourierCoefficient N k =
          summedRamanujanLayer N k / (fareyDenominatorCount N : ℂ)

def claim42704 : Prop :=
  ∀ (N : ℕ), 1 ≤ N →
    periodicEnergy N =
      gcdEnergy N / (12 * (fareyDenominatorCount N : ℝ) ^ 2)

def jordanTotientTwo (r : ℕ) : ℤ :=
  ∑ d ∈ r.divisors, (d : ℤ) ^ 2 * mobius (r / d)

def claim42707 : Prop :=
  ∀ (N : ℕ), 1 ≤ N →
    gcdEnergy N =
      ∑ r ∈ IccNat N,
        (jordanTotientTwo r : ℝ) *
          (∑ d ∈ (IccNat N).filter (fun d => r ∣ d),
            (mertens (N / d) : ℝ) / (d : ℝ)) ^ 2

def claim42710 : Prop :=
  ∀ (N : ℕ), 1 ≤ N →
    gcdEnergy N ≥
        (mertens N : ℝ) ^ 2 / (riemannZeta (2 : ℂ)).re ∧
      (mertens N : ℝ) ^ 2 / (riemannZeta (2 : ℂ)).re =
        (6 / (Real.pi : ℝ) ^ 2) * (mertens N : ℝ) ^ 2

def innovation (N d : ℕ) : ℤ :=
  levelWeight N d - levelWeight (N - 1) d

def claim42712 : Prop :=
  ∀ (N d : ℕ), 1 ≤ N → 1 ≤ d →
    innovation N d =
      if d ∣ N then mobius (N / d) else 0

def layerInner (m n : ℕ) : ℝ :=
  ∑ d ∈ IccNat m, ∑ e ∈ IccNat n,
    (innovation m d : ℝ) * (innovation n e : ℝ) * gcdKernel d e

def claim42714 : Prop :=
  ∀ (N : ℕ), 1 < N →
    layerInner N N =
      ∏ p ∈ N.primeFactors,
        (2 : ℝ) * (1 - (p : ℝ)⁻¹)

def localLayerFactor (p α β : ℕ) : ℝ :=
  if α = 0 ∧ β = 0 then 1
  else if α = β then
    2 * (1 - (p : ℝ)⁻¹)
  else if β = 0 then
    -((p : ℝ) - 1) * (p : ℝ) ^ (-α : ℤ)
  else if α = 0 then
    -((p : ℝ) - 1) * (p : ℝ) ^ (-β : ℤ)
  else
    -((p : ℝ) - 1) ^ 2 * (p : ℝ) ^ (-(Nat.dist α β : ℤ) - 1)

def claim42715 : Prop :=
  ∀ (m n : ℕ), 1 ≤ m → 1 ≤ n →
    layerInner m n =
      ∏ p ∈ (m.primeFactors ∪ n.primeFactors),
        localLayerFactor p (m.factorization p) (n.factorization p)

end MathlibPlus.Open.Research.FareyGcdEnergy
