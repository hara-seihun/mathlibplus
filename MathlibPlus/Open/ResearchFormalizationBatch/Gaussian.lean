import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch.Gaussian

open scoped BigOperators

noncomputable section

/-- The finite positive-node, positive-weight data occurring in the packet. -/
def gaussianRuleData (n : ℕ) (x w : Fin n → ℝ) : Prop :=
  0 < n ∧
    (∀ i j : Fin n, i.val < j.val → x i < x j) ∧
    (∀ i : Fin n, 0 < x i) ∧
    (∀ i : Fin n, 0 < w i)

def gaussianMoment {n : ℕ} (x w : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ j : Fin n, w j * (x j) ^ k

def momentHankel {n : ℕ} (x w : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun a b => gaussianMoment x w (a.val + b.val)

def claim42875 : Prop :=
  ∀ (n : ℕ) (x w : Fin n → ℝ),
    gaussianRuleData n x w →
      (∀ k : ℕ, gaussianMoment x w k = ∑ j : Fin n, w j * (x j) ^ k) ∧
      momentHankel x w = fun a b =>
        gaussianMoment x w (a.val + b.val)

def nodePolynomial {n : ℕ} (x : Fin n → ℝ) : Polynomial ℝ :=
  ∏ j : Fin n, (Polynomial.X - Polynomial.C (x j))

def reciprocalPolynomial {n : ℕ} (x : Fin n → ℝ) : Polynomial ℝ :=
  ∏ j : Fin n, (1 - Polynomial.C (x j) * Polynomial.X)

def vectorPolynomial {n : ℕ} (v : Fin n → ℝ) : Polynomial ℝ :=
  ∑ k : Fin n, Polynomial.C (v k) * Polynomial.X ^ k.val

def truncateBelow (n : ℕ) (p : Polynomial ℝ) : Polynomial ℝ :=
  Polynomial.ofFinsupp
    (AddMonoidAlgebra.ofCoeff
      (Finsupp.filter (M := ℝ) (fun k : ℕ => k < n) p.toFinsupp.coeff))

def truncatedNumerator {n : ℕ} (x v : Fin n → ℝ) : Polynomial ℝ :=
  truncateBelow n (reciprocalPolynomial x * vectorPolynomial v)

def claim42876 : Prop :=
  ∀ (n : ℕ) (x : Fin n → ℝ) (v : Fin n → ℝ),
    (∀ z : ℝ, z ≠ 0 →
      Polynomial.eval z (reciprocalPolynomial x) =
        z ^ n * Polynomial.eval z⁻¹ (nodePolynomial x)) ∧
    (∀ z : ℝ,
      Polynomial.eval z (vectorPolynomial v) =
        ∑ k : Fin n, v k * z ^ k.val) ∧
    (∀ k : ℕ, k < n →
      (truncatedNumerator x v).coeff k =
        (reciprocalPolynomial x * vectorPolynomial v).coeff k) ∧
    (∀ k : ℕ, n ≤ k → (truncatedNumerator x v).coeff k = 0)

def quadraticForm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : ℝ :=
  ∑ a : Fin n, v a * (∑ b : Fin n, M a b * v b)

def dualWeight {n : ℕ} (x w : Fin n → ℝ) (j : Fin n) : ℝ :=
  1 / (w j *
    (Polynomial.eval (x j) (Polynomial.derivative (nodePolynomial x))) ^ 2)

def oneHoleObservable {n : ℕ} (x v : Fin n → ℝ) (j : Fin n) : ℝ :=
  (x j) ^ (n - 1) * Polynomial.eval (x j)⁻¹ (truncatedNumerator x v)

def claim42878 : Prop :=
  ∀ (n : ℕ) (x w : Fin n → ℝ),
    gaussianRuleData n x w →
      ∀ v : Fin n → ℝ,
        quadraticForm (momentHankel x w)⁻¹ v =
          ∑ j : Fin n,
            ((x j) ^ 2 *
              (Polynomial.eval (x j)⁻¹ (truncatedNumerator x v)) ^ 2) /
              (w j *
                (Polynomial.eval (x j)⁻¹
                  (Polynomial.derivative (reciprocalPolynomial x))) ^ 2)

def claim42879 : Prop :=
  ∀ (n : ℕ) (x w : Fin n → ℝ) (v : Fin n → ℝ),
    (∀ j : Fin n,
      dualWeight x w j =
        1 / (w j *
          (Polynomial.eval (x j) (Polynomial.derivative (nodePolynomial x))) ^ 2)) ∧
    (∀ j : Fin n,
      oneHoleObservable x v j =
        (x j) ^ (n - 1) *
          Polynomial.eval (x j)⁻¹ (truncatedNumerator x v))

def claim42880 : Prop :=
  ∀ (n : ℕ) (x w : Fin n → ℝ),
    gaussianRuleData n x w →
      ∀ v : Fin n → ℝ,
        quadraticForm (momentHankel x w)⁻¹ v =
          ∑ j : Fin n, dualWeight x w j * (oneHoleObservable x v j) ^ 2

def vandermondeOn {n : ℕ} (x : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  ∏ i ∈ S, ∏ j ∈ S.filter (fun j => i.val < j.val), (x j - x i)

def partitionFunction {n : ℕ} (r : ℕ) (x w : Fin n → ℝ) : ℝ :=
  ∑ S ∈ ((Finset.univ : Finset (Fin n)).powerset).filter (fun S => S.card = r),
    (∏ i ∈ S, w i) * (vandermondeOn x S) ^ 2

def claim42881 : Prop :=
  ∀ (n : ℕ) (x w : Fin n → ℝ),
    gaussianRuleData n x w →
      ∀ j : Fin n,
        (∏ i ∈ (Finset.univ : Finset (Fin n)).erase j, w i) *
              (vandermondeOn x ((Finset.univ : Finset (Fin n)).erase j)) ^ 2 =
          partitionFunction (n := n) n x w * dualWeight x w j

end
end MathlibPlus.Open.ResearchFormalizationBatch.Gaussian
