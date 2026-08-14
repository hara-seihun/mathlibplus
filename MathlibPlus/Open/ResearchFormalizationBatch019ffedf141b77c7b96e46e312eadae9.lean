import Mathlib

namespace MathlibPlus
namespace Open
namespace ResearchFormalizationBatch

noncomputable def componentMonomial {V : Type} [Fintype V]
    (E : Finset (Sym2 V)) : MvPolynomial ℕ ℚ :=
  let G := SimpleGraph.fromEdgeSet (E : Set (Sym2 V))
  ∏ C : G.ConnectedComponent,
    letI : Fintype C.supp := Fintype.ofFinite C.supp
    MvPolynomial.X (Fintype.card C.supp)

noncomputable def unsignedConnectedSetPolynomial {V : Type} [Fintype V]
    (F : SimpleGraph V) : MvPolynomial ℕ ℚ :=
  letI : Fintype F.edgeSet := Fintype.ofFinite F.edgeSet
  ∑ E₀ ∈ F.edgeFinset.powerset, componentMonomial E₀

noncomputable def partialOne (p : MvPolynomial ℕ ℚ) : MvPolynomial ℕ ℚ :=
  p.support.sum fun d =>
    if d 1 = 0 then 0
    else
      MvPolynomial.C (d 1 : ℚ) *
        MvPolynomial.monomial (d - Finsupp.single 1 1) (p.coeff d)

noncomputable def markedSingletonPolynomial {V : Type} [Fintype V]
    (F : SimpleGraph V) : MvPolynomial ℕ ℚ :=
  partialOne (unsignedConnectedSetPolynomial F)

def unsignedMarkedSingletonIdentity : Prop :=
  ∀ {V : Type} [Fintype V] (F : SimpleGraph V),
    F.IsAcyclic →
      markedSingletonPolynomial F =
        ∑ v : V,
          let s : Set V := {w | w ≠ v}
          letI : Finite s := Finite.of_injective (fun w => w.1) Subtype.val_injective
          letI : Fintype s := Fintype.ofFinite _
          unsignedConnectedSetPolynomial (F.induce s)

end ResearchFormalizationBatch
end Open
end MathlibPlus
