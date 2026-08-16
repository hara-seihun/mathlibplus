import MathlibPlus.Open.Analysis.FormalizationBatchO0267

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.AnchoredPaleyWienerClaim15161

noncomputable section

/-- A Shannon-coordinate realization of a `PW_π` function. -/
def shannonRepresentation (a : ℤ → ℂ) (f : ℂ → ℂ) : Prop :=
  Summable (fun n : ℤ => ‖a n‖ ^ 2) ∧
    (∀ n : ℤ, a n = f (n : ℂ)) ∧
      ∀ z : ℂ,
        f z = ∑' n : ℤ,
          a n * MathlibPlus.Open.Analysis.FormalizationBatchO0267.pwCardinalSine z n

/-- The `PW_π` carrier in the packet's Shannon normalization. -/
def PWpi (f : ℂ → ℂ) : Prop :=
  ∃ a : ℤ → ℂ, shannonRepresentation a f

/-- The consecutive anchored subspace `V_M`. -/
def anchoredPW (M : ℕ) (f : ℂ → ℂ) : Prop :=
  PWpi f ∧ ∀ n : ℕ, n < M → f (n : ℂ) = 0

/-- The remaining Shannon-coordinate index set. -/
def exteriorIndex (M : ℕ) :=
  {n : ℤ // n < 0 ∨ (M : ℤ) ≤ n}

/-- The fixed harmless Shannon-column sign. -/
def exteriorColumnSign (n : ℤ) : ℂ :=
  (-1 : ℂ) ^ n.natAbs

/-- The normalized exterior Cauchy entry, with the removable integer value
at every exterior integer node filled in explicitly. -/
noncomputable def normalizedExteriorEntry (z : ℂ) (n : ℤ) : ℂ :=
  if z = (n : ℂ) then 1 else
    exteriorColumnSign n *
      (MathlibPlus.Open.Analysis.FormalizationBatch.normalizedRowFactor z /
        (Complex.ofReal Real.pi * (z - (n : ℂ))))

/-- The concrete normalized evaluation operator on the remaining Shannon
coordinates. -/
noncomputable def anchoredEvaluationOperator
    (M N : ℕ) (nodes : Fin N → ℂ) :
    (exteriorIndex M → ℂ) → (Fin N → ℂ) :=
  fun a j =>
    ∑' n : exteriorIndex M,
      normalizedExteriorEntry (nodes j) n.1 * a n

/-- Normalized evaluation at a complex node in the packet's evaluation norm. -/
noncomputable def normalizedEvaluation (z : ℂ) (f : ℂ → ℂ) : ℂ :=
  f z /
    Complex.ofReal
      (Real.sqrt
        (MathlibPlus.Open.Analysis.FormalizationBatch.normalizedSineDenominator z.im))

/-- Claim 15161.  The normalized evaluation of every anchored Shannon
function is exactly the exterior Cauchy operator on its remaining
coordinates, with the fixed column signs and removable integer values. -/
def claim15161 : Prop :=
  ∀ (M N : ℕ) (nodes : Fin N → ℂ) (a : ℤ → ℂ) (f : ℂ → ℂ),
    shannonRepresentation a f →
      (∀ n : ℕ, n < M → f (n : ℂ) = 0) →
        ∀ j : Fin N,
          normalizedEvaluation (nodes j) f =
            anchoredEvaluationOperator M N nodes
              (fun n : exteriorIndex M => a n.1) j

end

end MathlibPlus.Open.Analysis.AnchoredPaleyWienerClaim15161
