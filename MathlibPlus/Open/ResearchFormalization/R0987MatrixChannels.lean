import MathlibPlus.Open.ResearchFormalization.MatrixChannels

namespace MathlibPlus.Open.ResearchFormalization.R0987MatrixChannels

noncomputable section

open MathlibPlus.Open.ResearchFormalization.MatrixChannels

private def diagonalMatrix {ι : Type*} [DecidableEq ι]
    {𝕜 : Type*} [Field 𝕜] (D : Matrix ι ι 𝕜) : Prop :=
  ∀ i j, i ≠ j → D i j = 0

private def rowObservableChannel {𝕜 : Type*} [Field 𝕜]
    {m k : ℕ} (P : BlockPresentation 𝕜 m k)
    (D : Matrix (Fin m ⊕ Fin k) (Fin m ⊕ Fin k) 𝕜)
    (E : Matrix (Fin m) (Fin m) 𝕜) :
    Matrix (Fin m) (Fin m ⊕ Fin k) 𝕜 :=
  P.A * D - E * P.A

private def selectedDiagonal {𝕜 : Type*} [Field 𝕜]
    {m k : ℕ} (D : Matrix (Fin m ⊕ Fin k) (Fin m ⊕ Fin k) 𝕜) :
    Matrix (Fin m) (Fin m) 𝕜 :=
  fun i j => D (Sum.inl i) (Sum.inl j)

private def unselectedDiagonal {𝕜 : Type*} [Field 𝕜]
    {m k : ℕ} (D : Matrix (Fin m ⊕ Fin k) (Fin m ⊕ Fin k) 𝕜) :
    Matrix (Fin k) (Fin k) 𝕜 :=
  fun i j => D (Sum.inr i) (Sum.inr j)

private def stackedChannels {𝕜 : Type*} [Field 𝕜]
    {m k q : ℕ} (P : BlockPresentation 𝕜 m k)
    (D : Fin q → Matrix (Fin m ⊕ Fin k) (Fin m ⊕ Fin k) 𝕜)
    (E : Fin q → Matrix (Fin m) (Fin m) 𝕜) :
    Matrix (Fin m × Fin (q + 1)) (Fin m ⊕ Fin k) 𝕜 :=
  fun r c =>
    Fin.cases
      (P.A r.1 c)
      (fun i => (rowObservableChannel P (D i) (E i)) r.1 c)
      r.2

private def reducedChannels {𝕜 : Type*} [Field 𝕜]
    {m k q : ℕ} (P : BlockPresentation 𝕜 m k)
    (D : Fin q → Matrix (Fin m ⊕ Fin k) (Fin m ⊕ Fin k) 𝕜) :
    Matrix (Fin m × Fin q) (Fin k) 𝕜 :=
  fun r j =>
    ((quotientMatrix P) * unselectedDiagonal (D r.2) -
      selectedDiagonal (D r.2) * (quotientMatrix P)) r.1 j

/-- Claim 27942: stacking the full-row-rank A channel with every diagonal
commutator channel splits rank into the selected rank m and the stacked
reduced quotient channels. -/
def stackedChannelRankDecomposition_claim27942 : Prop :=
  ∀ (𝕜 : Type*) [Field 𝕜] (m k q : ℕ)
    (P : BlockPresentation 𝕜 m k)
    (D : Fin q → Matrix (Fin m ⊕ Fin k) (Fin m ⊕ Fin k) 𝕜)
    (E : Fin q → Matrix (Fin m) (Fin m) 𝕜),
    (∀ i, diagonalMatrix (D i)) →
    (∀ i, diagonalMatrix (E i)) →
    Matrix.rank (stackedChannels P D E) =
      m + Matrix.rank (reducedChannels P D)

/-- Claim 27944: after the exact kernel parametrization z=(-Kx,x), each
row-observable channel vanishes exactly when its selected/unselected quotient
channel vanishes. -/
def reducedKernelEquivalence_claim27944 : Prop :=
  ∀ (𝕜 : Type*) [Field 𝕜] (m k : ℕ)
    (P : BlockPresentation 𝕜 m k)
    (D : Matrix (Fin m ⊕ Fin k) (Fin m ⊕ Fin k) 𝕜)
    (E : Matrix (Fin m) (Fin m) 𝕜),
    diagonalMatrix D → diagonalMatrix E →
    ∀ x : Fin k → 𝕜,
      let z := blockVector (-(quotientMatrix P).mulVec x) x
      P.A.mulVec z = 0 →
        (rowObservableChannel P D E).mulVec z = 0 ↔
          ((quotientMatrix P) * unselectedDiagonal D -
            selectedDiagonal D * (quotientMatrix P)).mulVec x = 0

end

end MathlibPlus.Open.ResearchFormalization.R0987MatrixChannels
