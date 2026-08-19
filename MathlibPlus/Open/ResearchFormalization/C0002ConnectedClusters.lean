import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.C0002ConnectedClusters

noncomputable section

def extremalPolynomial (p : ℕ → ℕ → ℝ) (n : ℕ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (n + 1), Polynomial.C (p n k) * Polynomial.X ^ k

def clusterBase (p c : ℕ → ℕ → ℝ) : Prop :=
  (∀ n, p n 0 = 1) ∧
    (∀ n k, n < k → p n k = 0) ∧
    (∀ n, c n 0 = 0)

def clusterExponentialIdentity (p c : ℕ → ℕ → ℝ) : Prop :=
  clusterBase p c ∧
    ∀ n,
      Polynomial.toPowerSeries (extremalPolynomial p n) =
        (PowerSeries.exp ℝ).subst (PowerSeries.mk (c n))

def clusterDepthLocality : Prop :=
  ∀ (k : ℕ) (u v : ℕ → ℝ),
    u 0 = 0 →
      v 0 = 0 →
        (∀ j, j ≤ k → u j = v j) →
          PowerSeries.coeff k
              ((PowerSeries.exp ℝ).subst (PowerSeries.mk u)) =
            PowerSeries.coeff k
              ((PowerSeries.exp ℝ).subst (PowerSeries.mk v))

def formalConnectedClusterCoordinates_claim31
    (p c : ℕ → ℕ → ℝ) : Prop :=
  clusterExponentialIdentity p c ∧ clusterDepthLocality

def coefficientwiseExponentialRecurrence (p c : ℕ → ℕ → ℝ) : Prop :=
  ∀ (n k : ℕ),
    (k : ℝ) * p n k =
      ∑ j ∈ Finset.Icc 1 k, (j : ℝ) * c n j * p n (k - j)

def coefficientwiseClusterRecursion (p c : ℕ → ℕ → ℝ) : Prop :=
  ∀ (n k : ℕ),
    0 < k →
      c n k =
        p n k - (1 / (k : ℝ)) *
          ∑ j ∈ Finset.Ico 1 k, (j : ℝ) * c n j * p n (k - j)

def exactExponentialLogarithmTriangularRecursions_claim32 : Prop :=
  (∀ (p c : ℕ → ℕ → ℝ),
    clusterExponentialIdentity p c ↔
      clusterBase p c ∧ coefficientwiseExponentialRecurrence p c) ∧
    (∀ (p c : ℕ → ℕ → ℝ),
      clusterExponentialIdentity p c → coefficientwiseClusterRecursion p c)

def firstConnectedClusters_claim33 : Prop :=
  ∀ (p c : ℕ → ℕ → ℝ) (a : ℕ → ℝ),
    clusterExponentialIdentity p c →
      (∀ n, a n = p n 1) →
        ∀ n,
          c n 1 = a n ∧
            c n 2 = p n 2 - a n ^ 2 / 2 ∧
              c n 3 = p n 3 - a n * p n 2 + a n ^ 3 / 3

end

end MathlibPlus.Open.ResearchFormalization.C0002ConnectedClusters
