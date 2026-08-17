import Mathlib
import MathlibPlus.Open.TreeSpectral

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0310Claim19628

open MathlibPlus.Open.TreeSpectral

noncomputable section

/-- The leaf-deck, leaf-grafting, and grading operators on the verified
rational Finsupp tree spaces have their literal basis actions. -/
def claim19628 : Prop :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  ∀ n : ℕ,
    let L_n : TreeSpace n →ₗ[ℚ] TreeSpace (n - 1) := leafDeletion n
    let G_n : TreeSpace n →ₗ[ℚ] TreeSpace (n + 1) := graft n
    let N_n : TreeSpace n →ₗ[ℚ] TreeSpace n :=
      (n : ℚ) • (LinearMap.id : TreeSpace n →ₗ[ℚ] TreeSpace n)
    (∀ q : TreeClass n,
      let T := Quotient.out q
      L_n (Finsupp.single q 1) =
        ∑ ℓ : Fin n, ∑ u : TreeClass (n - 1),
          Finsupp.single u
            (if IsLeaf T.1 ℓ ∧
                GraphIso
                  (T.1.induce {x : Fin n | x ≠ ℓ})
                  (Quotient.out u).1 then
              1 else 0)) ∧
      (∀ q : TreeClass n,
        let T := Quotient.out q
        G_n (Finsupp.single q 1) =
          ∑ v : Fin n, ∑ u : TreeClass (n + 1),
            Finsupp.single u
              (if GraphIso (graftGraph T.1 v) (Quotient.out u).1 then
                1 else 0)) ∧
      (∀ v : TreeSpace n, N_n v = (n : ℚ) • v)

end

end MathlibPlus.Open.ResearchFormalization.R0310Claim19628
