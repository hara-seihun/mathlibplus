import MathlibPlus.Open.FormalizationBatch

namespace MathlibPlus.Open.ResearchFormalization.Claim8750

open scoped BigOperators

noncomputable section

/-- The terminal endpoint weight `nu_i` on the reviewed finite irreducible
Jacobi eigenvector carrier. -/
def terminalWeight8750
    (n : ℕ)
    (J : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (_hJ : MathlibPlus.Open.FormalizationBatch.IsFiniteIrreducibleJacobi n J)
    (x : ℝ)
    (v : Fin (n + 1) → ℝ)
    (_heigen : J.mulVec v = x • v)
    (_hnorm : (∑ k : Fin (n + 1), v k ^ 2) = 1) : ℝ :=
  |v (Fin.last n)| ^ 2

/-- The reversed endpoint polynomial `psi_r`, indexed by the reviewed
`n+1`-point basis and using its terminal endpoint. -/
def reversedEndpointPolynomial8750
    (n : ℕ)
    (J : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (_hJ : MathlibPlus.Open.FormalizationBatch.IsFiniteIrreducibleJacobi n J)
    (x : ℝ)
    (v : Fin (n + 1) → ℝ)
    (_heigen : J.mulVec v = x • v)
    (_hnorm : (∑ k : Fin (n + 1), v k ^ 2) = 1)
    (r : Fin (n + 1)) : ℝ :=
  v (MathlibPlus.Open.FormalizationBatch.reverseIndex n r) /
    v (Fin.last n)

/-- The reversed Christoffel kernel through the basis index `m`. -/
def reversedKernel8750
    (n : ℕ)
    (J : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (_hJ : MathlibPlus.Open.FormalizationBatch.IsFiniteIrreducibleJacobi n J)
    (x : ℝ)
    (v : Fin (n + 1) → ℝ)
    (_heigen : J.mulVec v = x • v)
    (_hnorm : (∑ k : Fin (n + 1), v k ^ 2) = 1)
    (m : Fin (n + 1)) : ℝ :=
  ∑ r : Fin (m.1 + 1),
    (reversedEndpointPolynomial8750 n J _hJ x v _heigen _hnorm
      (Fin.castLE (Nat.succ_le_of_lt m.isLt) r)) ^ 2

end

end MathlibPlus.Open.ResearchFormalization.Claim8750
