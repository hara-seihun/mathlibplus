import MathlibPlus.Open.Research.Q12PrimeCoverFormalization

namespace MathlibPlus.Open.Research.Q12PrimeCover

/-- Claim 41754: the normalized affine-lift harmlessness statement for the
inverse switch on the explicit prime-cover chart. -/
def claim41754 : Prop :=
  ∀ p : ℕ, Nat.Prime p → 3 < p →
    ∀ (lam : Q12Carrier → (ZMod p)ˣ) (τ : Q12Carrier → ZMod p),
      lam q12One = 1 → τ q12One = 0 →
      ∀ S : Set (PrimeCoverCarrier p),
        gpInverseClosed p S →
        gpDerivativeInvariant p lam τ q12SwitchInv q12Switch S →
        ∃ α : PrimeCoverCarrier p → PrimeCoverCarrier p,
          gpAutomorphism p α ∧
            Set.image α S =
              Set.image (gpAffineLift p lam τ q12SwitchInv) S

/-- Claim 41755: the inversion-closed projected derivative atoms are exactly
A and B. -/
def claim41755 : Prop :=
  q12ProjectedDerivativeAtoms q12Switch q12SwitchInv =
      {q12AtomA, q12AtomB} ∧
    q12AtomA ⊆ (Set.univ : Set Q12Carrier) \ {q12One} ∧
    q12AtomB ⊆ (Set.univ : Set Q12Carrier) \ {q12One}

/-- Claim 41756: complete derivative atoms occur in only the fixed C₄ axis
or all of Q₁₂, with the stated atom containment. -/
def claim41756 : Prop :=
  (∀ K : Set Q12Carrier, q12Subgroup K →
    (q12ContainsCompleteAtom K ↔
      K = q12Axis ∨ K = (Set.univ : Set Q12Carrier))) ∧
  q12AtomA ⊆ q12Axis ∧
  ¬ q12AtomB ⊆ q12Axis ∧
  q12AtomA ⊆ (Set.univ : Set Q12Carrier) ∧
  q12AtomB ⊆ (Set.univ : Set Q12Carrier)

/-- Claim 41757: the scalar stabilizer and prime-fibre saturation dichotomy. -/
def claim41757 : Prop :=
  ∀ p : ℕ, Nat.Prime p → 3 < p →
    ∀ lam : Q12Carrier → (ZMod p)ˣ,
      let Q := q12ScalarStabilizer p lam q12Switch
      (∀ h, h ∉ Q →
          ∃ k, q12DerivativeCoefficient p lam q12Switch h k ≠ 0) ∧
      (∀ h, h ∉ Q →
        (h ∈ q12AtomA →
          q12AtomSaturated p lam q12Switch q12AtomA) ∧
        (h ∈ q12AtomB →
          q12AtomSaturated p lam q12Switch q12AtomB)) ∧
      (Q ≠ q12Axis → Q ≠ (Set.univ : Set Q12Carrier) →
        q12AtomSaturated p lam q12Switch q12AtomA ∧
        q12AtomSaturated p lam q12Switch q12AtomB)

end MathlibPlus.Open.Research.Q12PrimeCover
