import Mathlib

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace MathlibPlus.Open.ResearchFormalizationBatch019ffedc64ac79c92719c0ad336498c

def graphAutomorphism (G : SimpleGraph (Fin 43))
    (σ : Equiv.Perm (Fin 43)) : Prop :=
  ∀ u v, G.Adj (σ u) (σ v) ↔ G.Adj u v

def vertexTransitive43 (G : SimpleGraph (Fin 43)) : Prop :=
  ∀ u v : Fin 43, ∃ σ : Equiv.Perm (Fin 43),
    graphAutomorphism G σ ∧ σ u = v

def graphAutomorphismSet (G : SimpleGraph (Fin 43)) :
    Finset (Equiv.Perm (Fin 43)) :=
  Finset.univ.filter (graphAutomorphism G)

def graphAutomorphismCard (G : SimpleGraph (Fin 43)) : ℕ :=
  (graphAutomorphismSet G).card

def isOrder43 (σ : Equiv.Perm (Fin 43)) : Prop :=
  σ ^ 43 = 1 ∧
    ∀ k : ℕ, 0 < k → k < 43 → σ ^ k ≠ 1

def isRegular43Cycle (σ : Equiv.Perm (Fin 43)) : Prop :=
  ∀ v : Fin 43, ∃ k : Fin 43, (σ^[k.val]) (0 : Fin 43) = v

def cyclicDifference43 (i j : Fin 43) : Fin 43 :=
  ⟨(j.val + 43 - i.val) % 43, Nat.mod_lt _ (by norm_num)⟩

def isCirculantAlong43 (G : SimpleGraph (Fin 43))
    (σ : Equiv.Perm (Fin 43)) : Prop :=
  ∃ S : Finset (Fin 43),
    ∀ i j : Fin 43,
      G.Adj ((σ^[i.val]) (0 : Fin 43)) ((σ^[j.val]) (0 : Fin 43)) ↔
        cyclicDifference43 i j ∈ S

/-- Claim 12658: prime-order vertex transitivity supplies a regular
43-cycle automorphism and a circulant relabeling. -/
def claim12658 : Prop :=
  ∀ G : SimpleGraph (Fin 43), vertexTransitive43 G →
    43 ∣ graphAutomorphismCard G ∧
    ∃ σ : Equiv.Perm (Fin 43),
      graphAutomorphism G σ ∧ isOrder43 σ ∧
        isRegular43Cycle σ ∧ isCirculantAlong43 G σ

def cyclicDistance43 (x y : ZMod 43) : ℕ :=
  let d := (x - y).val
  min d (43 - d)

def distanceRequirements43 (T : Finset (ZMod 43)) : Finset ℕ :=
  T.biUnion (fun x => (T.erase x).image (cyclicDistance43 x))

def distanceUniverse43 : Finset ℕ := Finset.Icc 1 21

def isFiveClique43 (S : Finset ℕ) (T : Finset (ZMod 43)) : Prop :=
  T.card = 5 ∧
    ∀ x ∈ T, ∀ y ∈ T, x ≠ y → cyclicDistance43 x y ∈ S

def isFiveIndependent43 (S : Finset ℕ) (T : Finset (ZMod 43)) : Prop :=
  T.card = 5 ∧
    ∀ x ∈ T, ∀ y ∈ T, x ≠ y → cyclicDistance43 x y ∉ S

/-- Claim 12660: an anchored five-set is a clique or independent exactly
when its ten cyclic-distance requirements lie in the mask or its complement. -/
def claim12660 : Prop :=
  ∀ T : Finset (ZMod 43), ∀ S : Finset ℕ,
    T.card = 5 → (0 : ZMod 43) ∈ T → S ⊆ distanceUniverse43 →
      ((isFiveClique43 S T ↔ distanceRequirements43 T ⊆ S) ∧
        (isFiveIndependent43 S T ↔
          ∀ d ∈ distanceRequirements43 T, d ∉ S))

def anchoredFiveSets43 : Finset (Finset (ZMod 43)) :=
  Finset.univ.filter (fun T => T.card = 5 ∧ (0 : ZMod 43) ∈ T)

def anchoredRequirementMasks43 : Finset (Finset ℕ) :=
  anchoredFiveSets43.image distanceRequirements43

/-- Claim 12661: the anchored census has the stated total and number of
requirement masks. -/
def claim12661 : Prop :=
  Nat.choose 42 4 = 111930 ∧
    anchoredFiveSets43.card = 111930 ∧
    anchoredRequirementMasks43.card = 10437

def allConnectionMasks43 : Finset (Finset ℕ) :=
  distanceUniverse43.powerset

def hasFiveCliqueMask43 (S : Finset ℕ) : Prop :=
  ∃ T : Finset (ZMod 43), isFiveClique43 S T

def hasFiveIndependentMask43 (S : Finset ℕ) : Prop :=
  ∃ T : Finset (ZMod 43), isFiveIndependent43 S T

/-- Claim 12662: the complete mask census has the two equal large classes and
no mask avoiding both a five-clique and a five-independent set. -/
def claim12662 : Prop :=
  let cliqueMasks := allConnectionMasks43.filter hasFiveCliqueMask43
  let independentMasks := allConnectionMasks43.filter hasFiveIndependentMask43
  let goodMasks := allConnectionMasks43.filter (fun S =>
    ¬ hasFiveCliqueMask43 S ∧ ¬ hasFiveIndependentMask43 S)
  let overlapMasks := allConnectionMasks43.filter (fun S =>
    hasFiveCliqueMask43 S ∧ hasFiveIndependentMask43 S)
  cliqueMasks.card = 1616836 ∧
    independentMasks.card = 1616836 ∧
    cliqueMasks.card = independentMasks.card ∧
    goodMasks.card = 0 ∧
    0 < overlapMasks.card

/-- A graph on 43 vertices is `(5,5)`-good when it has neither a five-clique
nor a five-independent set. -/
def isFiveFiveGood43 (G : SimpleGraph (Fin 43)) : Prop :=
  (¬ ∃ T : Finset (Fin 43), T.card = 5 ∧
    ∀ x ∈ T, ∀ y ∈ T, x ≠ y → G.Adj x y) ∧
  (¬ ∃ T : Finset (Fin 43), T.card = 5 ∧
    ∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ G.Adj x y)

/-- Claim 12663: no vertex-transitive graph of order 43 is `(5,5)`-good. -/
def claim12663 : Prop :=
  ∀ G : SimpleGraph (Fin 43), vertexTransitive43 G → ¬ isFiveFiveGood43 G

end MathlibPlus.Open.ResearchFormalizationBatch019ffedc64ac79c92719c0ad336498c
