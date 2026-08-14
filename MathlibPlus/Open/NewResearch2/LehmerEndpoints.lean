import Mathlib

namespace MathlibPlus.Open.NewResearch2.LehmerEndpoints

noncomputable section
open Classical
open scoped BigOperators

private abbrev IntegralOperator (n : Nat) := Matrix (Fin n) (Fin n) ℤ

private def eigenvalue {n : Nat} (A : IntegralOperator n) (T : ℝ) : Prop :=
  (∃ v : Fin n → ℝ, (∃ i : Fin n, v i ≠ 0) ∧
    ∀ i : Fin n, ∑ j : Fin n, (A i j : ℝ) * v j = T * v i)

private noncomputable def lehmerPolynomial : Polynomial ℤ :=
  Polynomial.X ^ 10 + Polynomial.X ^ 9 - Polynomial.X ^ 7 - Polynomial.X ^ 6 -
    Polynomial.X ^ 5 - Polynomial.X ^ 4 - Polynomial.X ^ 3 + Polynomial.X + 1

private noncomputable def lehmerNumber : ℝ :=
  sInf {x : ℝ |
    1 < x ∧ Polynomial.eval₂ (algebraMap ℤ ℝ) x lehmerPolynomial = 0}

private noncomputable def lehmerTraceBound : ℝ :=
  lehmerNumber + lehmerNumber⁻¹

private def oneExteriorTrace {n : Nat}
    (A : IntegralOperator n) (T : ℝ) : Prop :=
  2 < T ∧ T < lehmerTraceBound ∧ eigenvalue A T ∧
    (∀ x : ℝ, eigenvalue A x → x = T ∨ (-2 < x ∧ x < 2))

private def integralEndpointBranch {n : Nat}
    (A : IntegralOperator n) (T : ℝ) : Prop :=
  ∃ q : Polynomial ℤ,
    q.Monic ∧ Irreducible q ∧ q ∣ Matrix.charpoly A ∧
      Polynomial.eval₂ (algebraMap ℤ ℝ) T q = 0 ∧
      (∀ x : ℝ,
        Polynomial.eval₂ (algebraMap ℤ ℝ) x q = 0 →
          x = T ∨ (-2 ≤ x ∧ x ≤ 2))

def claim24448 : Prop :=
  ∀ (n : Nat) (A : IntegralOperator n) (T : ℝ),
    oneExteriorTrace A T →
      ∃ q : Polynomial ℤ,
        q.Monic ∧ Irreducible q ∧ q ∣ Matrix.charpoly A ∧
          Polynomial.eval₂ (algebraMap ℤ ℝ) T q = 0 ∧
          q.natDegree ≤ n ∧
          (∀ x : ℝ,
            Polynomial.eval₂ (algebraMap ℤ ℝ) x q = 0 →
              x = T ∨ (-2 < x ∧ x < 2))

def claim24452 : Prop :=
  ∀ (n : Nat) (A : IntegralOperator n) (T : ℝ),
    n ≤ 27 → oneExteriorTrace A T → ¬ integralEndpointBranch A T

end

end MathlibPlus.Open.NewResearch2.LehmerEndpoints
