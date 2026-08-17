import Mathlib
import MathlibPlus.Open.ResearchFormalizationBatch1831
import MathlibPlus.Open.ResearchFormalization.SeptenaryBatch

namespace MathlibPlus.Open.Combinatorics

open scoped MatrixGroups
open MathlibPlus.Open.ResearchFormalizationBatch1831
open MathlibPlus.Open.ResearchFormalization.Septenary

noncomputable section

/-- Claim 32710: every line-constant symmetric five-color Cayley structure
on `C₇²` is CI under the complete actual-color incidence graph, and all
1,595 full-automorphism representatives have singleton exact defect fibers. -/
def lineConstantC7ProfilesAreCI_claim32710 : Prop := by
  classical
  exact ∀ [Fact (Nat.Prime 7)],
    let Line := Projectivization (ZMod 7) V7
    let Color := Fin 5
    letI : Fintype Line := Fintype.ofFinite Line
    letI : DecidableEq Line := Classical.decEq Line
    let vertexColor : (Pair7 → Color) → Vertex7 → Option Color :=
      fun c v =>
        match v with
        | Sum.inl _ => none
        | Sum.inr p => some (c p)
    let profileColor : (Line → Color) → (Pair7 → Color) → Prop :=
      (fun profile c =>
        ∀ (p : Pair7) (x y : V7),
          x ∈ p.1 → y ∈ p.1 → x ≠ y →
          ∀ h : x - y ≠ 0,
            c p = profile (Projectivization.mk (ZMod 7) (x - y) h))
    let pglRelated : (Line → Color) → (Line → Color) → Prop :=
      fun profile other =>
        ∃ g : Matrix.ProjGenLinGroup (Fin 2) (ZMod 7),
          ∀ ell : Line, profile (g • ell) = other ell
    let incidenceIso :
        (Pair7 → Color) → (Pair7 → Color) → Prop :=
      fun c d =>
        ∃ e : Equiv.Perm Vertex7,
          (∀ v : Vertex7,
            vertexColor c v = vertexColor d (e v)) ∧
          (∀ v w : Vertex7,
            IncidenceAdjacent7 v w ↔ IncidenceAdjacent7 (e v) (e w))
    let graphRelated : (Line → Color) → (Line → Color) → Prop :=
      fun profile other =>
        ∃ c d : Pair7 → Color,
          profileColor profile c ∧ profileColor other d ∧ incidenceIso c d
    (Fintype.card V7 = 49 ∧
      Fintype.card Pair7 = 1176 ∧
      Fintype.card Vertex7 = 1225 ∧
      Fintype.card Line = 8 ∧
      Fintype.card (Line → Color) = 5 ^ 8 ∧
      (∀ profile : Line → Color, ∃! c : Pair7 → Color, profileColor profile c) ∧
      (∀ profile other : Line → Color,
        graphRelated profile other ↔ pglRelated profile other) ∧
      (∃ s : Setoid (Line → Color),
        (∀ a b : Line → Color,
          s.r a b ↔ pglRelated a b) ∧
        Nat.card (Quotient s) = 1595) ∧
      (∃ s : Setoid (Line → Color),
        (∀ a b : Line → Color,
          s.r a b ↔ graphRelated a b) ∧
        Nat.card (Quotient s) = 1595))

end
end MathlibPlus.Open.Combinatorics
