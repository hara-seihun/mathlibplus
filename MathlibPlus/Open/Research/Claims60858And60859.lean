import Mathlib

namespace MathlibPlus.Open.Research.FormalizationBatch

/-- Claim 60858: the finite-field difference-code interpolation statement. -/
def claim60858 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime],
    2 < p →
      ∀ (Y L : Type*)
        [AddCommGroup Y] [Module (ZMod p) Y]
        [FiniteDimensional (ZMod p) Y]
        [AddCommGroup L] [Module (ZMod p) L],
        Module.finrank (ZMod p) L = 1 →
          ∀ (s : Y → L),
            s 0 = 0 →
              let Δ : Y → Y → L := fun h x => s (x + h) - s x
              let M_s : Submodule (ZMod p) (Y → L) :=
                Submodule.span (ZMod p)
                  {w | (∃ c : L, w = fun _ => c) ∨
                    ∃ u t : Y, w = fun x => Δ u (x + t)}
              let P_s : Set Y := {h | ∃ c : L, ∀ x : Y, Δ h x = c}
              let M_s_pair : Set (Y → L) :=
                {w | ∀ x y : Y, ∃ m : Y → L,
                  m ∈ M_s ∧ (w x, w y) = (m x, m y)}
              ∃ P : Submodule (ZMod p) Y,
                (P : Set Y) = P_s ∧
                  (∃ sP : P →ₗ[ZMod p] L, ∀ h : P, sP h = s h) ∧
                    ∀ ℓ : Y →ₗ[ZMod p] L,
                      (∀ h : P, ℓ h = s h) →
                        (fun x => s x - ℓ x) ∈ M_s_pair

/-- Claim 60859: the binary-closure factorization through the line radical. -/
def claim60859 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime],
    2 < p →
      ∀ (Y L : Type*)
        [AddCommGroup Y] [Module (ZMod p) Y]
        [FiniteDimensional (ZMod p) Y]
        [AddCommGroup L] [Module (ZMod p) L],
        Module.finrank (ZMod p) L = 1 →
          ∀ (s : Y → L),
            s 0 = 0 →
              let Δ : Y → Y → L := fun h x => s (x + h) - s x
              let M_s : Submodule (ZMod p) (Y → L) :=
                Submodule.span (ZMod p)
                  {w | (∃ c : L, w = fun _ => c) ∨
                    ∃ u t : Y, w = fun x => Δ u (x + t)}
              let P_s : Set Y := {h | ∃ c : L, ∀ x : Y, Δ h x = c}
              ∀ ℓ : Y →ₗ[ZMod p] L,
                (∀ h : Y, h ∈ P_s → ℓ h = s h) →
                  let r : Y → L := fun y => s y - ℓ y
                  let Ω := L × Y
                  let q : (Y → L) → Ω → Ω :=
                    fun f z => (z.1 + f z.2, z.2)
                  let G : Set (Ω → Ω) :=
                    {g | Function.Bijective g ∧
                      ∃ m : Y → L, m ∈ M_s ∧
                        ∃ t : Y, g = fun z => (z.1 + m z.2, z.2 + t)}
                  let G2 : Set (Ω → Ω) :=
                    {g | Function.Bijective g ∧
                      ∀ x y : Ω, ∃ h : Ω → Ω, h ∈ G ∧
                        (g x, g y) = (h x, h y)}
                  q r ∈ G2 ∧
                    (∃ e : Ω ≃+ Ω, ∀ z : Ω, e z = q ℓ z) ∧
                      q s = fun z => q ℓ (q r z)

end MathlibPlus.Open.Research.FormalizationBatch
