import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch021Arithmetic

noncomputable section

abbrev PositiveNat := {n : ℕ // 0 < n}
abbrev ArithmeticHilbertSpace := PiLp (2 : ENNReal) (fun _ : PositiveNat => ℂ)

def arithmeticKet (n : PositiveNat) : ArithmeticHilbertSpace :=
  PiLp.single (2 : ENNReal) n (1 : ℂ)

def hArEigenvalue (n : PositiveNat) : ℂ := Complex.log (n.1 : ℂ)

def diagonalAction (d : PositiveNat → ℂ)
    (x y : ArithmeticHilbertSpace) : Prop :=
  ∀ n : PositiveNat, y n = d n * x n

def H_ar (x y : ArithmeticHilbertSpace) : Prop :=
  diagonalAction hArEigenvalue x y

def hArBasisAction (n : PositiveNat) : Prop :=
  H_ar (arithmeticKet n) (hArEigenvalue n • arithmeticKet n)

def expNegH_ar (s : ℂ) (n : PositiveNat) : ℂ :=
  Complex.exp (-s * hArEigenvalue n)

def expNegH_arAction (s : ℂ) (x y : ArithmeticHilbertSpace) : Prop :=
  diagonalAction (expNegH_ar s) x y

def operatorTrace (d : PositiveNat → ℂ) : ℂ :=
  ∑' n : PositiveNat, d n

def dirichletTerm (s : ℂ) (n : PositiveNat) : ℂ :=
  Complex.cpow (n.1 : ℂ) (-s)

def arithmeticHamiltonianSpec : Prop :=
  ∀ n : PositiveNat, hArBasisAction n

def claim_12703 : Prop :=
  arithmeticHamiltonianSpec ∧
  ∀ s : ℂ, 1 < s.re →
    operatorTrace (expNegH_ar s) = ∑' n : PositiveNat, dirichletTerm s n ∧
    (∑' n : PositiveNat, dirichletTerm s n) = riemannZeta s

end

end MathlibPlus.Open.ResearchFormalizationBatch021Arithmetic
