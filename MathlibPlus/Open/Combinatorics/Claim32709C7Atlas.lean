import Mathlib
import MathlibPlus.Open.ResearchFormalizationBatch1831
import MathlibPlus.Open.ResearchFormalization.SeptenaryBatch

namespace MathlibPlus.Open.Combinatorics

open scoped MatrixGroups
open MathlibPlus.Open.ResearchFormalizationBatch1831
open MathlibPlus.Open.ResearchFormalization.Septenary

noncomputable section

/-- Claim 32709: the complete line-constant five-color `C₇²` atlas, with
actual colors on all unordered pairs and exact PGL and colored-incidence
quotients. -/
def exactC7LineConstantAtlas_claim32709 : Prop := by
  classical
  exact ∀ [Fact (Nat.Prime 7)],
    let Line := Projectivization (ZMod 7) V7
    letI : Fintype Line := Fintype.ofFinite Line
    letI : DecidableEq Line := Classical.decEq Line
    let Color := Fin 5
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
    let width : (Line → Color) → ℕ :=
      fun profile => (Finset.univ.image profile).card
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
    let Profile : ℕ → Type :=
      fun k => {profile : Line → Color // width profile = k}
    let orbitRow : ℕ → ℕ → Prop := fun k expected =>
      ∃ s : Setoid (Profile k),
        (∀ a b : Profile k,
          s.r a b ↔ pglRelated a.1 b.1) ∧
        Nat.card (Quotient s) = expected
    let graphRow : ℕ → ℕ → Prop := fun k expected =>
      ∃ s : Setoid (Profile k),
        (∀ a b : Profile k,
          s.r a b ↔ graphRelated a.1 b.1) ∧
        Nat.card (Quotient s) = expected
    let allOrbitRow : ℕ → Prop := fun expected =>
      ∃ s : Setoid (Line → Color),
        (∀ a b : Line → Color,
          s.r a b ↔ pglRelated a b) ∧
        Nat.card (Quotient s) = expected
    let allGraphRow : ℕ → Prop := fun expected =>
      ∃ s : Setoid (Line → Color),
        (∀ a b : Line → Color,
          s.r a b ↔ graphRelated a b) ∧
        Nat.card (Quotient s) = expected
    (Fintype.card V7 = 49 ∧
      Fintype.card Pair7 = 1176 ∧
      Fintype.card Vertex7 = 1225 ∧
      Fintype.card Line = 8 ∧
      Fintype.card (Line → Color) = 5 ^ 8 ∧
      (∀ profile : Line → Color, ∃! c : Pair7 → Color, profileColor profile c) ∧
      Fintype.card (Profile 1) = 5 ∧
      Fintype.card (Profile 2) = 2540 ∧
      Fintype.card (Profile 3) = 57960 ∧
      Fintype.card (Profile 4) = 204120 ∧
      Fintype.card (Profile 5) = 126000 ∧
      orbitRow 1 5 ∧ orbitRow 2 80 ∧ orbitRow 3 390 ∧
        orbitRow 4 735 ∧ orbitRow 5 385 ∧
      graphRow 1 5 ∧ graphRow 2 80 ∧ graphRow 3 390 ∧
        graphRow 4 735 ∧ graphRow 5 385 ∧
      allOrbitRow 1595 ∧ allGraphRow 1595)

end
end MathlibPlus.Open.Combinatorics
