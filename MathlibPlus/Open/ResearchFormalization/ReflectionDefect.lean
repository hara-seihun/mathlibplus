import MathlibPlus.Combinatorics.StrongOrdering

namespace MathlibPlus.Open.ResearchFormalization

open MathlibPlus.Combinatorics

/-- Claim 48134: the two endpoint-forced copies of the unused set obey the
exact inclusion-exclusion overlap inequality. -/
def claim_48134 : Prop := by
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
        let X : Finset G :=
          (B.scanl (fun s a => s + a) 0).toFinset
        let T : G := B.sum
        let m : ℕ :=
          (U ∩ U.image (fun u : G => -T - u)).card
        let minusU : Finset G := U.image (fun u : G => -u)
        let totalPlusU : Finset G := U.image (fun u : G => T + u)
        r + 1 = X.card ∧
          X.card ≥ (minusU ∪ totalPlusU).card ∧
          (minusU ∪ totalPlusU).card = 2 * U.card - m

/-- Claim 48141: the reflection intersection has the exact lower bound obtained
by rearranging the overlap inequality. -/
def claim_48141 : Prop := by
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
        (m : ℤ) ≥ 2 * (t : ℤ) - 3 * (r : ℤ) - 1

end MathlibPlus.Open.ResearchFormalization
