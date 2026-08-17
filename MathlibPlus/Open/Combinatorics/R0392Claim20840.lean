import Mathlib
import MathlibPlus.Open.Combinatorics.R0392TraceExtension

open Classical

namespace MathlibPlus.Open.Combinatorics.R0392

noncomputable section

private def memberSupport {I V : Type*} [DecidableEq I] [DecidableEq V]
    [Fintype I]
    (X : Finset V) (C T : I → Finset V) (x : V) : Finset (Option I) :=
  (Finset.univ : Finset (Option I)).filter (fun o =>
    x ∈ extendedMember X C T o)

/-- Claim 20840: the support computed from the pivot extension is the dual
support of the arbitrary fixed-weight trace multihypergraph. -/
def pivotIncidenceSupports_are_code_dual_claim20840 : Prop :=
  ∀ {I V : Type*} [DecidableEq I] [DecidableEq V] [Fintype I]
    (X Y : Finset V) (C T : I → Finset V) (b p : ℕ),
    Function.Injective C →
      (∀ i : I, C i ⊆ Y ∧ (C i).card = b) →
        pairwiseIntersecting C →
          threeSunflowerFree C →
            Disjoint X Y →
              X.card = b + p →
                (∀ i : I, T i ⊆ X ∧ (T i).card = p) →
                  (∀ x : V, x ∈ X →
                    memberSupport X C T x =
                      insert none
                        (((Finset.univ : Finset I).filter
                            (fun i => x ∈ T i)).image some)) ∧
                    (∀ x y : V, x ∈ X → y ∈ X →
                      (memberSupport X C T x = memberSupport X C T y ↔
                        ∀ i : I, (x ∈ T i ↔ y ∈ T i)))

end

end MathlibPlus.Open.Combinatorics.R0392
