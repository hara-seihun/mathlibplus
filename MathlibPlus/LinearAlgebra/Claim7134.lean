import MathlibPlus.Basic

namespace MathlibPlus.LinearAlgebra.Claim7134

/-!
The source maps `G_n`, `Phi_n`, and the current carriers `H,Y,I,X` are not
defined in the claim record.  Their only required interface for the displayed
current decomposition is the two componentwise identities `phiI=I'+v` and
`phiX=X'+v`, which are retained as hypotheses.  Tensor squares and tensor
products are represented entrywise as outer products.
-/

/-- Entrywise expansion of the doubled-state current difference. -/
theorem doubledState_current_decomposition
    {R : Type*} [CommRing R] {n : ℕ}
    (phiI phiX I' X' v : Fin n → R)
    (hI : ∀ i, phiI i = I' i + v i)
    (hX : ∀ i, phiX i = X' i + v i) :
    (fun i j : Fin n => phiI i * phiI j - phiX i * phiX j) =
      (fun i j : Fin n =>
        I' i * I' j - X' i * X' j +
          (I' i - X' i) * v j + v i * (I' j - X' j)) := by
  funext i j
  rw [hI i, hX i, hI j, hX j]
  ring

end MathlibPlus.LinearAlgebra.Claim7134
