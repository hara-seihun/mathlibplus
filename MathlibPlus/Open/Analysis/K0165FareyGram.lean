import Mathlib

namespace MathlibPlus.Open.Analysis.K0165

open scoped BigOperators
noncomputable section

abbrev FareyFormalVector := ℕ+ →₀ ℝ

def fareyBasis (d : ℕ+) : FareyFormalVector :=
  Finsupp.single d 1

def gcdGramKernel (d e : ℕ+) : ℝ :=
  (((Nat.gcd (d : ℕ) (e : ℕ) : ℕ) : ℝ) ^ 2) /
    (((d : ℕ) : ℝ) * ((e : ℕ) : ℝ))

def gcdGramPairing (u v : FareyFormalVector) : ℝ :=
  ∑ d ∈ u.support, ∑ e ∈ v.support,
    (u d) * (v e) * gcdGramKernel d e

def positiveDivisors (n : ℕ+) : Finset ℕ+ :=
  (Finset.Icc (1 : ℕ+) n).filter (fun d => (d : ℕ) ∣ (n : ℕ))

def fareyLevel (n : ℕ+) : FareyFormalVector :=
  ∑ d ∈ positiveDivisors n,
    ((ArithmeticFunction.moebius ((n : ℕ) / (d : ℕ)) : ℤ) : ℝ) • fareyBasis d

def arithmeticWhiteningWeight (n : ℕ+) : ℝ :=
  ∏ p ∈ Nat.primeFactors (n : ℕ),
    (1 - (((p : ℝ) ^ 2)⁻¹))

def layerIndex (N : ℕ) (i : Fin N) : ℕ+ :=
  ⟨i.1 + 1, Nat.succ_pos i.1⟩

def fareyGramBlock (N : ℕ+) : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ :=
  fun i j => gcdGramPairing (fareyLevel (layerIndex (N : ℕ) i))
    (fareyLevel (layerIndex (N : ℕ) j))

def determinantEveryFiniteLayerGramBlock : Prop :=
  ∀ N : ℕ+,
    Matrix.det (fareyGramBlock N) =
      ∏ q ∈ Finset.Icc (1 : ℕ+) N, arithmeticWhiteningWeight q

end

end MathlibPlus.Open.Analysis.K0165
