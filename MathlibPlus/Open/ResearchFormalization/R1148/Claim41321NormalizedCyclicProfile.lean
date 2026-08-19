import Mathlib

open Classical

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.R1148.Claim41321

abbrev F7 := ZMod 7
abbrev V := F7 × F7
abbrev EPoint := V × Fin 3

private def translateKernelSet (B : Finset V) (v : V) : Finset V :=
  B.image (fun b => b + v)

private def tripleKernelSet (B : Finset V) : Finset V :=
  B.image (fun b => 3 • b)

private def profileConnectionSet
    (K B : Finset V) : Finset EPoint :=
  K.image (fun a => (a, (0 : Fin 3))) ∪
    B.image (fun a => (a, (1 : Fin 3))) ∪
      (tripleKernelSet B).image (fun a => (a, (2 : Fin 3)))

private def profileMap
    (ψ : Fin 3 → V → V) : EPoint → EPoint :=
  fun p => (ψ p.2 p.1, p.2)

private def profileImage
    (ψ : Fin 3 → V → V) (S : Finset EPoint) : Finset EPoint :=
  S.image (profileMap ψ)

private def extensionInverse (x : EPoint) : EPoint :=
  (-((2 : ZMod 7) ^ x.2.val)⁻¹ • x.1, -x.2)

private def inverseClosedProfileSet (S : Finset EPoint) : Prop :=
  ∀ x ∈ S, extensionInverse x ∈ S

private def normalizedKernelMap41321
    (ε : F7) (p : F7 → F7 → F7)
    (ψ : V → V) : Prop :=
  (ε = 1 ∨ ε = -1) ∧
    ψ (0, 0) = (0, 0) ∧
      ∀ x y : F7, ψ (x, y) = (ε * x, p x y)

private def normalizedQuotientIdentityCyclicProfile41321
    (K B C : Finset V)
    (ε : Fin 3 → F7)
    (p : Fin 3 → F7 → F7 → F7)
    (ψ : Fin 3 → V → V) : Prop :=
  (∀ i : Fin 3,
    normalizedKernelMap41321 (ε i) (p i) (ψ i) ∧
      Function.Bijective (ψ i)) ∧
    (K = ∅ ∨ K = Finset.univ) ∧
    inverseClosedProfileSet (profileConnectionSet K B) ∧
    inverseClosedProfileSet (profileConnectionSet K C) ∧
    profileImage ψ (profileConnectionSet K B) =
      profileConnectionSet K C

def doubleTranslate41321 (S : Set V) (z : V) : Set V :=
  {v | ∃ s ∈ S, v = s + 2 • z}

def claim41321 : Prop :=
  ∀ (K B C : Finset V)
    (ε : Fin 3 → F7)
    (p : Fin 3 → F7 → F7 → F7)
    (ψ : Fin 3 → V → V),
    normalizedQuotientIdentityCyclicProfile41321 K B C ε p ψ →
      let Bset : Set V := B
      (∀ (k : Fin 3) (z : V),
        Set.image (ψ (k + 1))
            (doubleTranslate41321 Bset z) =
          doubleTranslate41321
            (Set.image (ψ 1) Bset) (2 • ψ k z)) ∧
        (∃ Cset : Set V,
          (∀ i : Fin 3, Set.image (ψ i) Bset = Cset) ∧
            (∀ (k : Fin 3) (z : V),
              Set.image (ψ (k + 1))
                  (doubleTranslate41321 Bset z) =
                doubleTranslate41321
                  (Set.image (ψ (k + 1)) Bset) (2 • ψ k z)))

end MathlibPlus.Open.ResearchFormalization.R1148.Claim41321

end
