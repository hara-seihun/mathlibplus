import Mathlib

namespace MathlibPlus.Open.Research.FormalizationBatch14735

noncomputable section

/-- The weight-basis index for `M_k = Sym^k (ℂ²) ⊗ Sym^k (ℂ²)`. -/
abbrev TargetIndex (k : ℕ) := Fin (k + 1) × Fin (k + 1)

/-- Reversal of the weight basis of `Sym^k (ℂ²)`. -/
def reverseIndex (k : ℕ) (r : Fin (k + 1)) : Fin (k + 1) :=
  ⟨k - r.1, Nat.lt_succ_of_le (Nat.sub_le k r.1)⟩

/-- The factor-swap generator `s₀` on the target coefficient module. -/
def factorSwap (k : ℕ) : Matrix (TargetIndex k) (TargetIndex k) ℂ :=
  fun i j => if j = (i.2, i.1) then 1 else 0

/-- The left-reversal generator `s₁ = J_k ⊗ I` on the target coefficient module. -/
def leftReversal (k : ℕ) : Matrix (TargetIndex k) (TargetIndex k) ℂ :=
  fun i j => if j = (reverseIndex k i.1, i.2) then 1 else 0

/--
The ordered Pauli frame `(I, X, Z, iY)` for the source
`χ_(+,+) ⊕ χ_(+,-) ⊕ ρ₂`.  In this frame `s₀` is transpose, hence has
signs `(+1,+1,+1,-1)`.
-/
def sourceS0 : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal (fun i => if i.1 = 3 then (-1 : ℂ) else 1)

/-- In the ordered Pauli frame, `s₁` is left multiplication by `X`. -/
def sourceS1 : Matrix (Fin 4) (Fin 4) ℂ := fun i j =>
  if i.1 = 1 ∧ j.1 = 0 then 1
  else if i.1 = 0 ∧ j.1 = 1 then 1
  else if i.1 = 3 ∧ j.1 = 2 then -1
  else if i.1 = 2 ∧ j.1 = 3 then -1
  else 0

/-- A fourfold copy of an `s₁`-odd line has `s₁ = -I`; the Pauli source does not. -/
def sourceNotFourCopiesOfOneOddLine : Prop :=
  sourceS1 ≠ (-1 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-- The two generator relations for the finite `W(C₂) = D₈` target action. -/
def targetWeylRelations (k : ℕ) : Prop :=
  factorSwap k * factorSwap k = (1 : Matrix (TargetIndex k) (TargetIndex k) ℂ) ∧
    leftReversal k * leftReversal k = (1 : Matrix (TargetIndex k) (TargetIndex k) ℂ) ∧
    (factorSwap k * leftReversal k) ^ 4 =
      (1 : Matrix (TargetIndex k) (TargetIndex k) ℂ)

/-- The concrete source matrices satisfy the same finite Weyl presentation. -/
def sourceWeylRelations : Prop :=
  sourceS0 * sourceS0 = (1 : Matrix (Fin 4) (Fin 4) ℂ) ∧
    sourceS1 * sourceS1 = (1 : Matrix (Fin 4) (Fin 4) ℂ) ∧
    (sourceS0 * sourceS1) ^ 4 = (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-- A coordinate basis vector in the target weight grid. -/
def targetBasis (k : ℕ) (p : TargetIndex k) : TargetIndex k → ℂ :=
  fun q => if q = p then 1 else 0

/-- The four explicit Pauli boundary states in the target weight grid. -/
def pauliState (k : ℕ) (a : Fin 4) : TargetIndex k → ℂ :=
  match a.1 with
  | 0 => ∑ i : Fin (k + 1), targetBasis k (i, i)
  | 1 => ∑ i : Fin (k + 1), targetBasis k (reverseIndex k i, i)
  | 2 => ∑ i : Fin (k + 1),
      ((k : ℂ) - 2 * (i.1 : ℂ)) • targetBasis k (i, i)
  | _ => -∑ i : Fin (k + 1),
      ((k : ℂ) - 2 * (i.1 : ℂ)) • targetBasis k (reverseIndex k i, i)

/-- The matrix whose columns are the four explicit Pauli boundary states. -/
def pauliStateMatrix (k : ℕ) : Matrix (TargetIndex k) (Fin 4) ℂ :=
  fun p a => pauliState k a p

/--
The heterogeneous Pauli source is not four copies of one `s₁`-odd line and,
for every `k ≥ 1`, its displayed four-state map is an injective finite
`W(C₂)`-equivariant lift into `M_k`.  Equivariance is stated on the two
Coxeter generators, with the explicit coefficient-module actions above.
-/
def heterogeneousPauliSourceLift : Prop :=
  sourceNotFourCopiesOfOneOddLine ∧
    sourceWeylRelations ∧
    ∀ k : ℕ, 1 ≤ k →
      targetWeylRelations k ∧
        Function.Injective (Matrix.mulVec (pauliStateMatrix k)) ∧
          factorSwap k * pauliStateMatrix k = pauliStateMatrix k * sourceS0 ∧
          leftReversal k * pauliStateMatrix k = pauliStateMatrix k * sourceS1

end
end MathlibPlus.Open.Research.FormalizationBatch14735
