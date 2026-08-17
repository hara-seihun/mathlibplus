import MathlibPlus.Combinatorics.StrongOrdering

namespace MathlibPlus.Open.Combinatorics

open MathlibPlus.Combinatorics

/-- Claim 16765: the beyond-rectification small-set theorem. -/
def beyondRectificationSmallSet_claim16765 : Prop := by
  classical
  exact
    ∃ c : ℝ, 0 < c ∧
      ∃ p₀ : ℕ, ∀ p : ℕ, Nat.Prime p → p₀ ≤ p →
        ∀ A : Finset (ZMod p), 0 ∉ A →
          (A.card : ℝ) ≤
              Real.exp (c * Real.rpow (Real.log (p : ℝ)) (1 / 4 : ℝ)) →
            ∃ f : Fin A.card → ZMod p,
              Function.Injective f ∧
                Finset.univ.image f = A ∧
                  validOrdering (List.ofFn f)

/-- Claim 16771: small-set sequencing in finite abelian groups. -/
def smallAbelianGroupSequencing_claim16771 : Prop := by
  classical
  exact
    ∀ (G : Type*) [AddCommGroup G] [Finite G],
      (∀ A : Finset G, 0 ∉ A → A.card ≤ 20 →
        ∃ f : Fin A.card → G,
          Function.Injective f ∧
            Finset.univ.image f = A ∧
              validOrdering (List.ofFn f) ∧
                (∀ i, 0 < i → i < A.card →
                  ((List.ofFn f).take i).sum ≠ 0)) ∧
      (∀ A : Finset G, 0 ∉ A → A.card ≤ 22 → Finset.sum A (fun x : G => x) = 0 →
        ∃ f : Fin A.card → G,
          Function.Injective f ∧
            Finset.univ.image f = A ∧
              validOrdering (List.ofFn f) ∧
                (∀ i, 0 < i → i < A.card →
                  ((List.ofFn f).take i).sum ≠ 0))

/-- Claim 16773: nonzero field scaling transports valid orderings. -/
def fieldScalingPreservesValidOrdering_claim16773 : Prop := by
  classical
  exact
    ∀ p : ℕ, Nat.Prime p →
      (∀ x : ZMod p, -x = (-1 : ZMod p) * x) ∧
        ∀ c : ZMod p, c ≠ 0 →
          ∀ A : Finset (ZMod p), 0 ∉ A →
            ∀ f : Fin A.card → ZMod p,
              Function.Injective f ∧ Finset.univ.image f = A →
                Function.Injective (fun i : Fin A.card => c * f i) ∧
                  Finset.univ.image (fun i : Fin A.card => c * f i) =
                    A.image (fun x : ZMod p => c * x) ∧
                    (validOrdering (List.ofFn f) ↔
                      validOrdering
                        (List.map (fun x : ZMod p => c * x) (List.ofFn f)))

/-- Claim 16777: the quantified reflection-defect inequality. -/
def quantifiedReflectionDefectInequality_claim16777 : Prop := by
  classical
  exact
    ∀ {G : Type*} [AddCommGroup G] (A : Finset G) (B : List G),
      0 ∉ A →
      B.Nodup →
      (∀ x ∈ B, x ∈ A) →
      strongOrdering B →
      (∀ u ∈ A, u ∉ B →
        ∀ k : ℕ, k ≤ B.length →
          ¬ strongOrdering (B.take k ++ [u] ++ B.drop k)) →
        let U : Finset G := A \ B.toFinset
        let r : ℕ := B.length
        let t : ℕ := A.card
        let T : G := B.sum
        let m : ℕ :=
          (U ∩ U.image (fun u : G => -T - u)).card
        3 * (r : ℤ) ≥ 2 * (t : ℤ) - (m : ℤ) - 1

end MathlibPlus.Open.Combinatorics
