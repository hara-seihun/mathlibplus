import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch0602.Semilattice

noncomputable section

private def batchJoinIrreducible {α : Type*} [SemilatticeSup α] (x : α) : Prop :=
  ∀ ⦃a b : α⦄, x = a ⊔ b → x = a ∨ x = b

private noncomputable def batchJoinIrreducibleCount
    (α : Type*) [Fintype α] [SemilatticeSup α] : ℕ :=
  letI : DecidablePred (fun x : α => batchJoinIrreducible x) :=
    fun x => Classical.propDecidable (batchJoinIrreducible x)
  (Finset.univ.filter (fun x : α => batchJoinIrreducible x)).card

/-- Claim 23998: a finite join-semilattice with `M` elements has at least
`ceil(log₂ M)` join-irreducibles, with the stated 58-element instance. -/
def finiteJoinSemilatticeIrreducibleFloor : Prop :=
  (∀ (α : Type*) [Fintype α] [SemilatticeSup α],
      Nat.clog 2 (Fintype.card α) ≤ batchJoinIrreducibleCount α) ∧
  (∀ (α : Type*) [Fintype α] [SemilatticeSup α],
      Fintype.card α = 58 →
        6 ≤ batchJoinIrreducibleCount α)

end
end MathlibPlus.Open.ResearchFormalizationBatch0602.Semilattice
