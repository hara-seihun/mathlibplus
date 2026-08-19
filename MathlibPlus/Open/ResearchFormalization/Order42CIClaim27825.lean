import MathlibPlus.Open.ResearchFormalization.Order42Batch

namespace MathlibPlus.Open.ResearchFormalization.Order42CIRepair

noncomputable section

private def cayleyGraph (S : Finset Order42) : SimpleGraph Order42 :=
  SimpleGraph.fromRel (fun x y => x ≠ y ∧ y - x ∈ S)

private def automorphismImage (φ : Order42 ≃+ Order42)
    (S : Finset Order42) : Finset Order42 :=
  S.map φ.toEquiv.toEmbedding

/-- Every inverse-closed connection set on the exact order-42
`C₇ × S₃` carrier satisfies the undirected CI criterion. -/
def c7TimesS3UndirectedCI_claim27825 : Prop :=
  ∀ S : Finset Order42, S ∈ connectionSets →
    ∀ T : Finset Order42, T ∈ connectionSets →
      Nonempty (SimpleGraph.Iso (cayleyGraph S) (cayleyGraph T)) →
        ∃ φ : Order42 ≃+ Order42,
          T = automorphismImage φ S

end

end MathlibPlus.Open.ResearchFormalization.Order42CIRepair
