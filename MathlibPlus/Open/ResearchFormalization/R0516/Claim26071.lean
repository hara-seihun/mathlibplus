import MathlibPlus.Open.ResearchFormalization.R0516Claim26072
import MathlibPlus.Open.ResearchFormalization.R0516Claim26074
import MathlibPlus.Open.Combinatorics.FixedSupportClaim26067

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0516.Claim26071

noncomputable section

open MathlibPlus.Open.Combinatorics.FixedSupportClaim26067
open MathlibPlus.Open.ResearchFormalization.R0516Claim26072

/-- Remove the two marked variables from a full monomial exponent while
retaining every residual `G^(2)` color variable. -/
def residualExponent
    (m : (ColorVar 3) →₀ ℕ) : (ColorVar 3) →₀ ℕ :=
  m - Finsupp.single (xVar 3 1) (m (xVar 3 1)) -
    Finsupp.single (zVar 3 1) (m (zVar 3 1))

/-- The literal partial coefficient of `gDegreeTwo` at the marked variables;
its coefficients are the actual `MvPolynomial.coeff` values of `G^(2)` and
its residual monomials are not relabelled. -/
def coefficientPolynomial {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (k : ℕ) : MvPolynomial (ColorVar 3) ℤ :=
  (gDegreeTwo T).support.sum (fun m =>
    if m (xVar 3 1) = k ∧ m (zVar 3 1) = k - 1 then
      MvPolynomial.monomial (residualExponent m) ((gDegreeTwo T).coeff m)
    else 0)

/-- The supports represented by the exact `x₁^k z₁^(k-1)` coloring filter of
`gDegreeTwo`. -/
def coefficientSupportSet {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (k : ℕ) : Set (Finset V) :=
  {S | ∃ c : V → Fin 3,
    gDegreeTwoCoefficientFilter T k c ∧ supportOfColor c = S}

/-- The connected nonempty `k`-vertex supports of the host tree. -/
def connectedSupportSet {V : Type*} [DecidableEq V]
    (T : SimpleGraph V) (k : ℕ) : Set (Finset V) :=
  {S | S.card = k ∧ S.Nonempty ∧
    (T.induce (S : Set V)).Preconnected}

/-- Claim 26071: induced supports in a tree are forests, edge number `k-1`
characterizes connectedness, and the exact coefficient coloring filter has
precisely the connected nonempty support carrier. -/
def claim26071 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (k : ℕ),
    T.IsTree → 1 ≤ k →
      (∀ S : Finset V,
        S.card = k →
          (T.induce (S : Set V)).IsAcyclic ∧
            ((internalEdges T S).card = k - 1 ↔
              (T.induce (S : Set V)).Preconnected)) ∧
      (∀ c : V → Fin 3,
        gDegreeTwoCoefficientFilter T k c ↔
          supportOfColor c ∈ connectedSupportSet T k) ∧
      coefficientSupportSet T k = connectedSupportSet T k ∧
        (coefficientPolynomial T k ≠ 0 ↔
          (connectedSupportSet T k).Nonempty)

end

end MathlibPlus.Open.ResearchFormalization.R0516.Claim26071
