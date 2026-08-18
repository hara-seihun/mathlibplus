import MathlibPlus.Open.Algebra.WeightedAlphabetSevenClaim26001

open scoped BigOperators

noncomputable section

open Classical

namespace MathlibPlus.Open.ResearchFormalization.R0503Claim26003

open MathlibPlus.Open.Algebra.WeightedAlphabetSevenClaim26001

abbrev Index := MathlibPlus.Open.Algebra.WeightedAlphabetSevenClaim26001.Index
abbrev Composition := MathlibPlus.Open.Algebra.WeightedAlphabetSevenClaim26001.Composition

/-- The monomial `t^d` on the exact interval carrier. -/
def powerFunction (N d : ℕ) : Index N → ℚ :=
  fun t => (t.1 : ℚ) ^ d

/-- The reflected coupling `h=-2k-k*` on the same fixed-total interval. -/
def coupledPairFunction (N : ℕ) (k : Index N → ℚ) : Index N → ℚ :=
  fun t => -2 * k t - k (reflectIndex N t)

def incidenceCount (r : ℕ) (J : Finset (Fin 7)) : ℚ :=
  ∑ I ∈ subsetFamily 7 r,
    if J ⊆ I then 1 else 0

/-- The coefficient contributed by a support `J` in the displayed
`3S₁-2S₂+S₃-S₅+2S₆` combination. -/
def tripleIncidenceCoefficient (J : Finset (Fin 7)) : ℚ :=
  3 * incidenceCount 1 J -
    2 * incidenceCount 2 J +
      incidenceCount 3 J -
        incidenceCount 5 J + 2 * incidenceCount 6 J

/-- The coupled triple residual before replacing the reflected pair by its
fixed-total complementary block. -/
def coupledTripleResidual (N : ℕ) (h k : Index N → ℚ)
    (μ : Composition 7 N) : ℚ :=
  3 * blockSum 1 k μ +
    blockSum 2 h μ +
      blockSum 3 k μ +
        2 * blockSum 6 k μ

/-- The displayed residual after inserting `h=-2k-k*`. -/
def expandedTripleResidual (N d : ℕ) (μ : Composition 7 N) : ℚ :=
  let k := powerFunction N d
  3 * blockSum 1 k μ -
    2 * blockSum 2 k μ +
      blockSum 3 k μ -
        blockSum 5 k μ +
          2 * blockSum 6 k μ

/-- Claim 26003: for the exact seven-part fixed-total composition carrier,
the coupled quintic monomials have incidence coefficient three at every
nonconstant support size and the resulting residual is `3N^d`; the constant
triple functional has constant residual as well. -/
def claim26003 : Prop :=
  (∀ (N d : ℕ), 1 ≤ d → d ≤ 5 →
    let k := powerFunction N d
    let h := coupledPairFunction N k
    (∀ μ : Composition 7 N,
      coupledTripleResidual N h k μ = expandedTripleResidual N d μ) ∧
      (∀ r : ℕ, 1 ≤ r → r ≤ d →
        ∀ J : Finset (Fin 7), J.card = r →
          tripleIncidenceCoefficient J = 3) ∧
      (∀ μ : Composition 7 N,
        coupledTripleResidual N h k μ = 3 * (N : ℚ) ^ d)) ∧
  (∀ N : ℕ,
    ∃ c : ℚ, ∀ μ : Composition 7 N,
      coupledTripleResidual N
        (coupledPairFunction N (powerFunction N 0))
        (powerFunction N 0) μ = c)

end MathlibPlus.Open.ResearchFormalization.R0503Claim26003

end
