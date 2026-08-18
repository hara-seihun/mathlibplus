import MathlibPlus.Open.Research.FormalizationBatchUPolynomial

namespace MathlibPlus.Open.ResearchFormalization.Q0042Claim16079

open scoped BigOperators

noncomputable section

private abbrev PositiveIndex := {n : ℕ // 0 < n}

private def pathGraph16079 (m : ℕ) : SimpleGraph (Fin m) :=
  SimpleGraph.fromRel (fun i j => i.1 + 1 = j.1 ∨ j.1 + 1 = i.1)

private def castMvQRingHom16079 :
    MvPolynomial ℕ ℤ →+* MvPolynomial ℕ ℚ :=
  MvPolynomial.map (Int.castRingHom ℚ)

private def castMvQ16079 (p : MvPolynomial ℕ ℤ) : MvPolynomial ℕ ℚ :=
  castMvQRingHom16079 p

/-- The exact path-polynomial carrier `U_{P_m}`. -/
private def pathU16079 (m : ℕ) : MvPolynomial ℕ ℚ :=
  castMvQ16079
    (MathlibPlus.Open.ResearchFormalizationBatch.forestUPolynomial
      (pathGraph16079 m))

private def pathUsesOnlyEarlier16079 (n : PositiveIndex)
    (p : MvPolynomial ℕ ℚ) : Prop :=
  ∀ m ∈ p.support, ∀ i : ℕ,
    m i ≠ 0 → 0 < i ∧ i < n.1

private def pathTriangularity16079 : Prop :=
  ∀ n : PositiveIndex, ∃ p : MvPolynomial ℕ ℚ,
    pathU16079 n.1 = MvPolynomial.X n.1 + p ∧
      pathUsesOnlyEarlier16079 n p

private def pathMonomial16079 (parts : Multiset PositiveIndex) :
    MvPolynomial ℕ ℚ :=
  (parts.map (fun n => pathU16079 n.1)).prod

private def positiveRename16079 (N : ℕ) (hN : 0 < N) (n : ℕ) : Fin N :=
  ⟨(n - 1) % N, Nat.mod_lt _ hN⟩

private def finitePathCoordinate16079 (N : ℕ) (hN : 0 < N)
    (i : Fin N) : MvPolynomial (Fin N) ℚ :=
  MvPolynomial.rename (positiveRename16079 N hN)
    (pathU16079 (i.1 + 1))

private def finiteTriangularShape16079 (N : ℕ) (hN : 0 < N) : Prop :=
  ∀ i : Fin N, ∃ p : MvPolynomial (Fin N) ℚ,
    finitePathCoordinate16079 N hN i = MvPolynomial.X i + p ∧
      ∀ m ∈ p.support, ∀ j : Fin N,
        m j ≠ 0 → j.1 < i.1

private def finitePolynomialAutomorphism16079 (N : ℕ) (hN : 0 < N) : Prop :=
  ∃ e : MvPolynomial (Fin N) ℚ ≃ₐ[ℚ] MvPolynomial (Fin N) ℚ,
    ∀ i : Fin N,
      e (MvPolynomial.X i) = finitePathCoordinate16079 N hN i

/-- Claim 16079: the actual path U-polynomials are triangular in the named
variables, every finite positive coordinate change is a polynomial
automorphism, and the resulting path monomials are linearly independent. -/
def claim16079_triangularPathPolynomialCoordinates : Prop :=
  pathTriangularity16079 ∧
    (∀ (N : ℕ) (hN : 0 < N),
      finiteTriangularShape16079 N hN ∧
        finitePolynomialAutomorphism16079 N hN) ∧
      LinearIndependent ℚ pathMonomial16079

end

end MathlibPlus.Open.ResearchFormalization.Q0042Claim16079
