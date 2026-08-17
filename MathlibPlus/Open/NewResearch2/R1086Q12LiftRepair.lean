import Mathlib
import MathlibPlus.Open.Research.Q12CIBatch

namespace MathlibPlus.Open.NewResearch2.R1086Q12LiftRepair

noncomputable section

private def inversePairDistinct {p k : ℕ}
    (r : Fin k → ZMod p) : Prop :=
  (∀ i : Fin k, r i ≠ 0) ∧
    ∀ i j : Fin k, i ≠ j → r i ≠ r j ∧ r i ≠ -r j

private def productConnection {p k : ℕ} {G : Type*} [Group G]
    (r : Fin k → ZMod p) (c : G → Fin (k + 1)) : Set (ZMod p × G) :=
  {z | ∃ i : Fin k, ∃ h : G,
      c h = Fin.succ i ∧ z = (r i, h)} ∪
    {z | ∃ i : Fin k, ∃ h : G,
      c h = Fin.succ i ∧ z = (-r i, h⁻¹)}

private def colorPreservingIsoAtMostThree {G : Type*} [Group G]
    (k : ℕ) (c d : G → Fin (k + 1)) (e : Equiv G G) : Prop :=
  e 1 = 1 ∧
    ∀ (i : Fin (k + 1)) (x y : G),
      (c (x⁻¹ * y) = i ↔ d ((e x)⁻¹ * e y) = i)

/-- Claim 28752: odd-prime lifts using at most three distinct inverse-pair
carriers are automorphic whenever their fixed-color Q₁₂ data are isomorphic. -/
def claim28752 : Prop :=
  ∀ (p : ℕ), Nat.Prime p → 2 < p →
    ∀ {G : Type*} [Group G] [Fintype G]
      (a b : G),
      MathlibPlus.Open.Research.Q12.isQ12Presentation a b →
      ∀ (k : ℕ), k ≤ 3 →
        ∀ (r : Fin k → ZMod p),
          inversePairDistinct r →
          ∀ (c d : G → Fin (k + 1)),
            c 1 = 0 → d 1 = 0 →
            ∀ e : Equiv G G,
              colorPreservingIsoAtMostThree k c d e →
                ∃ φ : G ≃* G,
                  (∀ h : G, c h = d (φ h)) ∧
                    Set.image (fun z : ZMod p × G => (z.1, φ z.2))
                      (productConnection r c) =
                    productConnection r d

end

end MathlibPlus.Open.NewResearch2.R1086Q12LiftRepair
