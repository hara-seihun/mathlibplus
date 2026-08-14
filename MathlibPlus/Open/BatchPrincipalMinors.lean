import Mathlib

namespace MathlibPlus.Open.PrincipalMinors

noncomputable def minor {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ)
    (I J : Finset (Fin r)) (h : I.card = J.card) : ℝ :=
  Matrix.det (B.submatrix
    (fun k => ((Finset.equivFin I).symm k : Fin r))
    (fun k => ((Finset.equivFin J).symm (Fin.cast h k) : Fin r)))

noncomputable def principalMinor {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ)
    (S : Finset (Fin r)) : ℝ := minor B S S rfl

def strictlyTotallyPositive {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ) : Prop :=
  ∀ (k : ℕ) (I J : Fin k → Fin r),
    StrictMono I → StrictMono J →
      0 < Matrix.det (fun i j => B (I i) (J j))

def incomparableSubsets {r : ℕ} (S T : Finset (Fin r)) : Prop :=
  ¬ S ⊆ T ∧ ¬ T ⊆ S

noncomputable def crossMinor {r : ℕ}
    (B : Matrix (Fin r) (Fin r) ℝ) (I : Finset (Fin r))
    (i j : Fin r) (hi : i ∉ I) (hj : j ∉ I) : ℝ :=
  minor B (insert j I) (insert i I) (by simp [hi, hj])

def strictPrincipalMinorLogSupermodular : Prop :=
  ∀ {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ),
    strictlyTotallyPositive B →
      principalMinor B ∅ = 1 ∧
      (∀ S : Finset (Fin r), principalMinor B S > 0) ∧
      (∀ (I : Finset (Fin r)) (i j : Fin r)
        (hi : i ∉ I) (hj : j ∉ I) (_hij : i ≠ j),
        principalMinor B (insert i I) * principalMinor B (insert j I) -
            principalMinor B I * principalMinor B (insert i (insert j I)) =
          crossMinor B I i j hi hj * crossMinor B I j i hj hi ∧
        0 < crossMinor B I i j hi hj * crossMinor B I j i hj hi) ∧
      (∀ S T : Finset (Fin r), incomparableSubsets S T →
        principalMinor B S * principalMinor B T >
          principalMinor B (S ∩ T) * principalMinor B (S ∪ T)) ∧
      (∀ (c : ℝ) (mass : Finset (Fin r) → ℝ), 0 < c →
        (∀ S : Finset (Fin r), mass S = c * principalMinor B S) →
        ∀ S T : Finset (Fin r), incomparableSubsets S T →
          mass S * mass T > mass (S ∩ T) * mass (S ∪ T))

end MathlibPlus.Open.PrincipalMinors
