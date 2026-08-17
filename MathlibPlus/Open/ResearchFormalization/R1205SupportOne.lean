import MathlibPlus.Open.Research.FormalizationBatchR1260

namespace MathlibPlus.Open.ResearchFormalization.R1205SupportOne

abbrev Cp (p : ℕ) := Multiplicative (ZMod p)
abbrev A4 := alternatingGroup (Fin 4)
abbrev CpA4 (p : ℕ) := Cp p × A4

/-- The exact normalized common-coordinate data used by the support-one claims. -/
def normalizedSupportOneData (p : ℕ)
    (q : Equiv.Perm A4) (σ : A4 → Equiv.Perm (Cp p))
    (f : CpA4 p → CpA4 p) : Prop :=
  q 1 = 1 ∧
    σ 1 = 1 ∧
      (∀ x : Cp p, ∀ h : A4,
        f (x, h) = (σ h x, q h)) ∧
        (∀ h₁ h₂ : A4,
          σ h₁ ≠ 1 → σ h₂ ≠ 1 → h₁ = h₂)

/-- Inverse closure of a connection set. -/
def inverseClosed {G : Type*} [Group G] (S : Set G) : Prop :=
  ∀ g, g ∈ S → g⁻¹ ∈ S

/-- Multiplication by a sign on the multiplicative presentation of `Cₚ`. -/
def signedFiberMap (p : ℕ) (ε : ZMod p) (x : Cp p) : Cp p :=
  Multiplicative.ofAdd (ε * Multiplicative.toAdd x)

/-- The product map in the conclusion of Claim 32237. -/
def productMap (p : ℕ) (ε : ZMod p) (α : A4 ≃* A4) : CpA4 p → CpA4 p :=
  fun z => (signedFiberMap p ε z.1, α z.2)

/-- The product-map automorphism condition, with the actual multiplication law. -/
def productMapAutomorphism (p : ℕ) (ε : ZMod p) (α : A4 ≃* A4) : Prop :=
  Function.Bijective (productMap p ε α) ∧
    ∀ x y : CpA4 p,
      productMap p ε α (x * y) = productMap p ε α x * productMap p ε α y

/-- Claim 32237: every normalized support-one map satisfying the ordinary
undirected Cayley-isomorphism hypotheses is transported by a product
automorphism with prime-factor sign `+1` or `-1`. -/
def claim32237 : Prop :=
  ∀ (p : ℕ), Nat.Prime p → 5 ≤ p →
    ∀ (q : Equiv.Perm A4) (σ : A4 → Equiv.Perm (Cp p))
      (f : CpA4 p → CpA4 p),
      normalizedSupportOneData p q σ f →
      ∀ S : Set (CpA4 p),
        inverseClosed S →
        inverseClosed (f '' S) →
        MathlibPlus.Open.Research.cayleyRelationIso S (f '' S) f →
        ∃ ε : ZMod p, (ε = 1 ∨ ε = -1) ∧
          ∃ α : A4 ≃* A4,
            productMapAutomorphism p ε α ∧
              productMap p ε α '' S = f '' S

end MathlibPlus.Open.ResearchFormalization.R1205SupportOne
