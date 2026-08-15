import Mathlib

namespace MathlibPlus.Open.Algebra.Claim6756

open scoped BigOperators

variable {p : ℕ} {G : Type*}

noncomputable def additiveAutomorphismMaps [AddCommGroup G] : Set (G → G) :=
  Set.range (fun e : G ≃+ G => (e : G → G))

noncomputable def generalLinearMaps (R : Type*) [Semiring R] [AddCommGroup G]
    [Module R G] : Set (G → G) :=
  Set.range (fun e : G ≃ₗ[R] G => (e : G → G))

noncomputable def inverseClosed [AddCommGroup G] (S : Finset G) : Prop :=
  ∀ x, x ∈ S ↔ -x ∈ S

noncomputable def characterSpectrum [AddCommGroup G] [Fintype G]
    (S : Finset G) : Multiset ℂ := by
  classical
  exact Multiset.map (fun χ : AddChar G ℂ => Finset.sum S (fun s => χ s))
    (Finset.univ : Finset (AddChar G ℂ)).1

noncomputable def orderedAdditivePairCount [AddCommGroup G] (S : Finset G) (g : G) : ℕ := by
  classical
  exact ((S.product S).filter (fun q : G × G => q.1 + q.2 = g)).card

noncomputable def convolutionProfile [AddCommGroup G] [Fintype G]
    (S : Finset G) : Multiset ℕ :=
  Multiset.map (orderedAdditivePairCount S) (Finset.univ : Finset G).1

noncomputable def profileMismatch [AddCommGroup G] [Fintype G]
    (S T : Finset G) : Prop :=
  characterSpectrum S ≠ characterSpectrum T ∨ convolutionProfile S ≠ convolutionProfile T

noncomputable def elementaryAbelianAutomorphismsAreGeneralLinear
    (p : ℕ) [Fact p.Prime] (G : Type*) [AddCommGroup G] [Fintype G]
    [Module (ZMod p) G] [FiniteDimensional (ZMod p) G] : Prop :=
  additiveAutomorphismMaps (G := G) = generalLinearMaps (ZMod p) ∧
    ∀ S T : Finset G,
      inverseClosed S → inverseClosed T → profileMismatch S T →
        (¬ ∃ e : G ≃+ G, S.map e.toEquiv.toEmbedding = T) ∧
        (¬ ∃ e : G ≃ₗ[ZMod p] G, S.map e.toEquiv.toEmbedding = T)

end MathlibPlus.Open.Algebra.Claim6756
