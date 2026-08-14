import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.GroupTheory.SpecificGroups.Alternating

namespace MathlibPlus.Open.GraphTheory

abbrev ResearchC5 := Multiplicative (ZMod 5)
abbrev ResearchA4 := alternatingGroup (Fin 4)
abbrev ResearchC5A4 := ResearchC5 × ResearchA4

private def completeMultipartiteConnection : Set ResearchC5A4 :=
  {g | g.1 ≠ 1}

private def completeMultipartiteGraph : SimpleGraph ResearchC5A4 :=
  SimpleGraph.mulCayley completeMultipartiteConnection

private def graphAutomorphismResearch (p : Equiv.Perm ResearchC5A4) : Prop :=
  ∀ x y,
    completeMultipartiteGraph.Adj (p x) (p y) ↔
      completeMultipartiteGraph.Adj x y

private def wreathMemberResearch (p : Equiv.Perm ResearchC5A4) : Prop :=
  ∃ σ : Equiv.Perm ResearchC5, ∀ x,
    (p x).1 = σ x.1

private def naturalHallOrbitResearch
    (x y : ResearchC5A4) : Prop :=
  ∃ a : ResearchC5, y = (a, 1) * x

private def naturalPartMovedResearch
    (p : Equiv.Perm ResearchC5A4) : Prop :=
  ∃ x y,
    naturalHallOrbitResearch x y ∧
      ¬ naturalHallOrbitResearch (p x) (p y)

/-- The connected `C₅ × A₄` complete-multipartite witness and its full
imprimitive wreath automorphism group. -/
def completeMultipartiteMarkRecoveryCounterexampleResearch2979 : Prop :=
  Fintype.card ResearchA4 = 12 ∧
    Fintype.card ResearchC5A4 = 60 ∧
    (∀ x y,
      completeMultipartiteGraph.Adj x y ↔
        x ≠ y ∧ x.1 ≠ y.1) ∧
    completeMultipartiteGraph.Connected ∧
    (∀ p : Equiv.Perm ResearchC5A4,
      graphAutomorphismResearch p ↔ wreathMemberResearch p) ∧
    (∀ x y,
      naturalHallOrbitResearch x y ↔ x.2 = y.2) ∧
    ∃ (a : ResearchC5) (a' : ResearchC5)
      (h₁ h₂ : ResearchA4),
      a ≠ a' ∧ h₁ ≠ h₂ ∧
      let τ := Equiv.swap (a, h₁) (a, h₂)
      graphAutomorphismResearch τ ∧ naturalPartMovedResearch τ

private def orbitalResearch (p : ResearchC5A4 × ResearchC5A4) :
    Set (ResearchC5A4 × ResearchC5A4) :=
  {q | ∃ a : Equiv.Perm ResearchC5A4,
    graphAutomorphismResearch a ∧
      q = (a p.1, a p.2)}

private def isFullOrbitalResearch
    (O : Set (ResearchC5A4 × ResearchC5A4)) : Prop :=
  ∃ p, O = orbitalResearch p

private noncomputable def orbitalMarkResearch
    (O : Set (ResearchC5A4 × ResearchC5A4))
    (L : Set (Equiv.Perm ResearchC5A4)) : Nat := by
  classical
  exact ((Finset.univ : Finset (ResearchC5A4 × ResearchC5A4)).filter
    (fun p => p ∈ O ∧ ∃ l, l ∈ L ∧ l p.1 = p.2)).card

private def conjugatePermutationSetResearch
    (τ : Equiv.Perm ResearchC5A4)
    (L : Set (Equiv.Perm ResearchC5A4)) : Set (Equiv.Perm ResearchC5A4) :=
  {p | ∃ l, l ∈ L ∧ p = τ * l * τ⁻¹}

/-- Every full-orbital/subgroup mark is blind to the within-part
transposition; the equality is equivariance under an actual graph
automorphism, while the natural Hall partition is moved. -/
def completeMultipartiteOrbitalSchemeMarkBlindnessResearch2979 : Prop :=
  completeMultipartiteMarkRecoveryCounterexampleResearch2979 ∧
    ∀ (τ : Equiv.Perm ResearchC5A4),
      graphAutomorphismResearch τ →
      ∀ (L : Subgroup (Equiv.Perm ResearchC5A4)),
        (∀ l : L, ∃ g : ResearchC5A4,
          ∀ x, l.1 x = g * x) →
        ∀ (O : Set (ResearchC5A4 × ResearchC5A4)),
          isFullOrbitalResearch O →
          orbitalMarkResearch O (L : Set (Equiv.Perm ResearchC5A4)) =
            orbitalMarkResearch O
              (conjugatePermutationSetResearch τ
                (L : Set (Equiv.Perm ResearchC5A4)))

end MathlibPlus.Open.GraphTheory
