import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch_01a006da

/-- Claim 10628: assembly of the completed gamma rows. -/
def gammaAggregateAssembly (α : ℝ) (w : ℕ → ℝ) : Prop :=
  0 < α →
    (∀ q : ℕ,
      Summable (fun p : ℕ =>
        w p * (Finset.prod (Finset.range p) (fun i => α + (q : ℝ) + i)))) →
    ((∀ q : ℕ,
        ∑' p : ℕ,
          w p *
            (Finset.prod (Finset.range (p + q)) (fun i => α + i)) /
              (Nat.factorial (2 * q) : ℝ) =
          (Finset.prod (Finset.range q) (fun i => α + i)) /
            (Nat.factorial (2 * q) : ℝ)) ↔
      (∀ q : ℕ,
        ∑' p : ℕ,
          w p * (Finset.prod (Finset.range p) (fun i => α + (q : ℝ) + i)) = 1))

/-- Claim 10682: the canonical shell assignments for shells beginning at two. -/
def canonicalShellLaw (w r : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    w n = (n : ℝ) ^ (-(1 : ℝ) / 2) ∧
    r n = (n : ℝ) ^ (-(2 : ℝ))

/-- Claim 60141: the prime-Fourier projection-histogram obstruction. -/
def primeFourierProjectionHistogramObstruction
    (p : ℕ) [Fact p.Prime]
    (V : Type*) [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V] [Fintype V]
    [Fintype (V →ₗ[ZMod p] ZMod p)]
    (S T : Set V) : Prop :=
  (0 ∉ S ∧ 0 ∉ T ∧
      (∀ s : V, s ∈ S → -s ∈ S) ∧
      (∀ t : V, t ∈ T → -t ∈ T)) →
    (∃ e : V ≃ V,
      ∀ x y : V,
        (x ≠ y ∧ y - x ∈ S) ↔
          (e x ≠ e y ∧ e y - e x ∈ T)) →
      let histogram (U : Set V) (ell : V →ₗ[ZMod p] ZMod p) : ZMod p → ℕ :=
        fun j => (U ∩ {x : V | ell x = j}).ncard
      let sectionSize (U : Set V) (ell : V →ₗ[ZMod p] ZMod p) : ℕ :=
        (U ∩ {x : V | ell x = 0}).ncard
      Multiset.map (histogram S) (Finset.univ : Finset (V →ₗ[ZMod p] ZMod p)).1 =
          Multiset.map (histogram T) (Finset.univ : Finset (V →ₗ[ZMod p] ZMod p)).1 ∧
        Multiset.map (sectionSize S) (Finset.univ : Finset (V →ₗ[ZMod p] ZMod p)).1 =
          Multiset.map (sectionSize T) (Finset.univ : Finset (V →ₗ[ZMod p] ZMod p)).1

/-- Claim 60142: the ordinary undirected Cayley CI statement for the presented group. -/
def eC35C8OrdinaryUndirectedCI : Prop :=
  let A := FreeGroup (Fin 2)
  let a₀ : A := FreeGroup.of (0 : Fin 2)
  let t₀ : A := FreeGroup.of (1 : Fin 2)
  let R : Set A := {a₀ ^ 35, t₀ ^ 8, t₀ * a₀ * t₀⁻¹ * a₀}
  let G := A ⧸ Subgroup.normalClosure R
  ∀ S T : Set G,
    (1 ∉ S ∧ 1 ∉ T ∧
        (∀ s : G, s ∈ S → s⁻¹ ∈ S) ∧
        (∀ t : G, t ∈ T → t⁻¹ ∈ T) ∧
        S.ncard = 6 ∧ T.ncard = 6) →
      (∃ e : G ≃ G,
        ∀ x y : G,
          (x ≠ y ∧ x⁻¹ * y ∈ S) ↔
            (e x ≠ e y ∧ (e x)⁻¹ * e y ∈ T)) →
        ∃ α : G ≃* G, α '' S = T

end MathlibPlus.Open.ResearchFormalizationBatch_01a006da
