import Mathlib
import MathlibPlus.Open.ResearchFormalization.R0848LeafChannels

namespace MathlibPlus.Open.ResearchFormalization.R0848

noncomputable section
open Classical

/-- The Hamiltonian-parity nullity prescribed for the three-channel prefixes. -/
def epsilon25277 (n : ℕ) : ℕ :=
  if n % 2 = 1 then 0 else Nat.factorial (n - 1) / 2

/-- The rational dimension of the kernel of the labelled three-channel prefix
attachment matrix. -/
noncomputable def threeChannelPrefixKernelDimension (n L : ℕ) : ℕ :=
  letI : Fintype (TreePrefix n L) := Fintype.ofFinite _
  letI : Fintype (RowPrefix n L 3) := Fintype.ofFinite _
  Module.finrank ℚ
    (LinearMap.ker
      (Matrix.toLin' (threeChannelLeafPrefixAttachmentMatrix n L)))

/-- Claim 25278: the exact rational nullities of every labelled three-channel
leaf prefix through order seven, including the displayed finite table. -/
def claim25278 : Prop :=
  (∀ (n L : ℕ),
    (3 ≤ n ∧ n ≤ 7) →
      (2 ≤ L ∧ L ≤ n - 1) →
        threeChannelPrefixKernelDimension n L = epsilon25277 n) ∧
  threeChannelPrefixKernelDimension 3 2 = 0 ∧
  (∀ L : ℕ, (L = 2 ∨ L = 3) →
    threeChannelPrefixKernelDimension 4 L = 3) ∧
  (∀ L : ℕ, (L = 2 ∨ L = 3 ∨ L = 4) →
    threeChannelPrefixKernelDimension 5 L = 0) ∧
  (∀ L : ℕ, (L = 2 ∨ L = 3 ∨ L = 4 ∨ L = 5) →
    threeChannelPrefixKernelDimension 6 L = 60) ∧
  (∀ L : ℕ, (L = 2 ∨ L = 3 ∨ L = 4 ∨ L = 5 ∨ L = 6) →
    threeChannelPrefixKernelDimension 7 L = 0)

end
end MathlibPlus.Open.ResearchFormalization.R0848
