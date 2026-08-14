import Mathlib

namespace MathlibPlus.Open.Attachment

abbrev OrientedEdge := {p : Fin 5 × Fin 5 // p.1 ≠ p.2}
abbrev EdgeFree (K : Type*) [Zero K] := OrientedEdge →₀ K

variable (K : Type*) [Field K]

noncomputable def edgeBasis (a b : Fin 5) (h : a ≠ b) : EdgeFree K :=
  Finsupp.single ⟨(a, b), h⟩ 1

noncomputable def antisymmetryGenerator (a b : Fin 5) (h : a ≠ b) : EdgeFree K :=
  edgeBasis K a b h + edgeBasis K b a h.symm

noncomputable def antisymmetrySubmodule : Submodule K (EdgeFree K) :=
  Submodule.span K (Set.range fun p : {p : Fin 5 × Fin 5 // p.1 ≠ p.2} =>
    antisymmetryGenerator K p.1.1 p.1.2 p.2)

abbrev OrientedEdgeSpace := EdgeFree K ⧸ antisymmetrySubmodule K

noncomputable def orientedEdge (a b : Fin 5) : OrientedEdgeSpace K :=
  if h : a = b then 0 else
    Submodule.Quotient.mk (p := antisymmetrySubmodule K) (edgeBasis K a b h)

noncomputable def puncturedStarRow (a m : Fin 5) : OrientedEdgeSpace K :=
  (Finset.univ.filter (fun b : Fin 5 => b ≠ a ∧ b ≠ m)).sum (fun b => orientedEdge K a b)

noncomputable def puncturedStarRowsSpan : Prop :=
  (2 : K) ≠ 0 →
    Submodule.span K (Set.range fun p : {p : Fin 5 × Fin 5 // p.1 ≠ p.2} =>
      puncturedStarRow K p.1.1 p.1.2) = ⊤

abbrev SpiderIndex :=
  {p : Fin 5 × Fin 5 × Fin 5 //
    p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2}

noncomputable def spiderCollapseMap : (SpiderIndex →₀ K) →ₗ[K] OrientedEdgeSpace K :=
  Finsupp.linearCombination K (fun s : SpiderIndex =>
    orientedEdge K s.1.1 s.1.2.1)

noncomputable def labelledSpiderCollapse : Prop :=
  Fintype.card SpiderIndex = 60 ∧
    Module.finrank K (OrientedEdgeSpace K) = 10 ∧
    LinearMap.range (spiderCollapseMap K) = ⊤

end MathlibPlus.Open.Attachment
