import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0761Claim24557

noncomputable section

abbrev C2 := Multiplicative (ZMod 2)
abbrev ElementaryTwoKernel (d : ℕ) := Fin d → C2
abbrev DihedralCarrier (d : ℕ) := ElementaryTwoKernel d × Bool
abbrev ElementaryTwoCarrier (d : ℕ) := Fin d → C2

def dihOne {d : ℕ} : DihedralCarrier d := (1, false)

def dihMul {d : ℕ} (g h : DihedralCarrier d) : DihedralCarrier d :=
  (g.1 * (if g.2 then fun i => (h.1 i)⁻¹ else h.1), xor g.2 h.2)

def dihInv {d : ℕ} (g : DihedralCarrier d) : DihedralCarrier d :=
  (if g.2 then g.1 else fun i => (g.1 i)⁻¹, g.2)

def inverseClosed {d : ℕ} (S : Set (DihedralCarrier d)) : Prop :=
  ∀ g, g ∈ S ↔ dihInv g ∈ S

def identityFree {d : ℕ} (S : Set (DihedralCarrier d)) : Prop :=
  dihOne ∉ S

def cayleyAdjacency {d : ℕ}
    (S : Set (DihedralCarrier d))
    (g h : DihedralCarrier d) : Prop :=
  dihMul (dihInv g) h ∈ S

def cayleyGraphIsomorphism {d : ℕ}
    (S T : Set (DihedralCarrier d)) : Prop :=
  ∃ e : Equiv.Perm (DihedralCarrier d),
    ∀ g h, cayleyAdjacency S g h ↔ cayleyAdjacency T (e g) (e h)

def dihedralAutomorphism {d : ℕ} (e : Equiv.Perm (DihedralCarrier d)) : Prop :=
  e dihOne = dihOne ∧ ∀ g h, e (dihMul g h) = dihMul (e g) (e h)

def mapsConnectionSet {d : ℕ}
    (e : Equiv.Perm (DihedralCarrier d))
    (S T : Set (DihedralCarrier d)) : Prop :=
  ∀ g, g ∈ S ↔ e g ∈ T

def undirectedCIGroup {d : ℕ} : Prop :=
  ∀ S T : Set (DihedralCarrier d),
    inverseClosed S → identityFree S →
    inverseClosed T → identityFree T →
    cayleyGraphIsomorphism S T →
    ∃ e : Equiv.Perm (DihedralCarrier d),
      dihedralAutomorphism e ∧ mapsConnectionSet e S T

def nonCIWitness {d : ℕ} : Prop :=
  ∃ S T : Set (DihedralCarrier d),
    inverseClosed S ∧ identityFree S ∧
    inverseClosed T ∧ identityFree T ∧
    cayleyGraphIsomorphism S T ∧
    ¬ ∃ e : Equiv.Perm (DihedralCarrier d),
      dihedralAutomorphism e ∧ mapsConnectionSet e S T

def kernelToElementaryCoordinates {d : ℕ}
    (g : DihedralCarrier d) : ElementaryTwoCarrier (d + 1) :=
  fun i =>
    if h : i.val < d then g.1 ⟨i.val, h⟩
    else if g.2 then Multiplicative.ofAdd 1 else Multiplicative.ofAdd 0

def dihedralElementaryTwoIsomorphism (d : ℕ) : Prop :=
  ∃ e : DihedralCarrier d ≃ ElementaryTwoCarrier (d + 1),
    (∀ g h, kernelToElementaryCoordinates (d := d) (dihMul g h) =
      fun i => e g i * e h i) ∧
    (∀ g, e g = kernelToElementaryCoordinates g)

/-- Claim 24557: the inversion semidirect product on an elementary-two kernel
is the elementary-two group of one higher rank, is already non-CI at rank five,
and remains non-CI for every rank at least five. -/
def elementaryTwoRankFiveAndAboveExcluded_claim24557 : Prop :=
  dihedralElementaryTwoIsomorphism 5 ∧
  nonCIWitness (d := 5) ∧
  (∀ d : ℕ, 5 ≤ d → nonCIWitness (d := d))

end

end MathlibPlus.Open.ResearchFormalization.R0761Claim24557
