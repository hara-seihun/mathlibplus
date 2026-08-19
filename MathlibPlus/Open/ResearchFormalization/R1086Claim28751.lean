import Mathlib
import MathlibPlus.Open.Research.Q12CIBatch

namespace MathlibPlus.Open.ResearchFormalization.R1086

noncomputable section

private def inversePairDistinct {p k : ℕ}
    (r : Fin k → ZMod p) : Prop :=
  (∀ i : Fin k, r i ≠ 0) ∧
    ∀ i j : Fin k, i ≠ j → r i ≠ r j ∧ r i ≠ -r j

/-- The lifted product connection set with one named inverse-pair carrier for
 each nonzero color. -/
def inversePairConnection {p k : ℕ} {G : Type*} [Group G]
    (r : Fin k → ZMod p) (c : G → Fin (k + 1)) :
    Set (ZMod p × G) :=
  {z | ∃ i : Fin k, ∃ h : G,
      c h = Fin.succ i ∧ z = (r i, h)} ∪
    {z | ∃ i : Fin k, ∃ h : G,
      c h = Fin.succ i ∧ z = (-r i, h⁻¹)}

def productInverse {p : ℕ} {G : Type*} [Group G]
    (z : ZMod p × G) : ZMod p × G :=
  (-z.1, z.2⁻¹)

def inverseClosedProduct {p : ℕ} {G : Type*} [Group G]
    (S : Set (ZMod p × G)) : Prop :=
  ∀ z, z ∈ S ↔ productInverse z ∈ S

/-- Claim 28751: for an odd cyclic-modulus carrier, at most three distinct
inverse-pair colours give exactly the displayed inverse-closed lift over any
finite Q12 presentation. -/
def claim28751 : Prop :=
  ∀ (p : ℕ), Odd p →
    ∀ {G : Type*} [Group G] [Fintype G]
      (a b : G),
      MathlibPlus.Open.Research.Q12.isQ12Presentation a b →
      ∀ (k : ℕ), k ≤ 3 →
        ∀ (r : Fin k → ZMod p),
          inversePairDistinct r →
          ∀ c : G → Fin (k + 1),
            (0, 1) ∉ inversePairConnection r c ∧
              inverseClosedProduct (inversePairConnection r c)

end
end MathlibPlus.Open.ResearchFormalization.R1086
