import Mathlib

namespace MathlibPlus.Open.Research.R0377

noncomputable section

/--
The complete ordered profile at an injectively ordered root tuple: the first
component is the labeled graph induced on the roots, and the second component
records the exact multiplicity of every outside-neighborhood cell.
-/
def completeOrderedRootProfile {n r : ℕ} (G : SimpleGraph (Fin n))
    (roots : Fin r → Fin n) (_hroots : Function.Injective roots) :
    SimpleGraph (Fin r) × (Finset (Fin r) → ℕ) :=
  (SimpleGraph.fromRel (fun i j => G.Adj (roots i) (roots j)),
    fun B => Set.ncard
      {v : Fin n | v ∉ Set.range roots ∧
        ∀ i : Fin r, (G.Adj (roots i) v ↔ i ∈ B)})

end
end MathlibPlus.Open.Research.R0377
