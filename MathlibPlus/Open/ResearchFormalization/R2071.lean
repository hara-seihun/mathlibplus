import Mathlib
import MathlibPlus.Open.CompleteGraphDual.BatchR1892

open scoped BigOperators
open Filter Topology

namespace MathlibPlus.Open.ResearchFormalization.R2071

noncomputable section

/-- A backbone word chooses one vertex in each of the `t` complete-graph blocks. -/
abbrev BackboneWord (M t : ℕ) := Fin t → Fin M

/-- A backbone coordinate is a block together with one of its two-element edge
coordinates.  The edge ground is the actual complete-graph-dual ground set. -/
abbrev EdgeCoordinate (M : ℕ) :=
  {e : Finset (Fin M) //
    e ∈ MathlibPlus.Open.CompleteGraphDual.edgeGround M}

abbrev BackboneCoordinate (M t : ℕ) := Σ j : Fin t, EdgeCoordinate M

/-- The noncomputable finite ordering used for the cyclic layer.  Its domain
is the actual word set, not an independently supplied family of members. -/
noncomputable def wordOrdering (M t : ℕ) : BackboneWord M t ≃ Fin (M ^ t) := by
  let e := Fintype.equivFin (BackboneWord M t)
  exact e.trans
    (Equiv.cast (by simp [BackboneWord]) :
      Fin (Fintype.card (BackboneWord M t)) ≃ Fin (M ^ t))

noncomputable def wordIndex {M t : ℕ} (u : BackboneWord M t) : Fin (M ^ t) :=
  wordOrdering M t u

/-- The product of the complete-graph-dual stars in the disjoint blocks. -/
def backboneMember {M t : ℕ} (u : BackboneWord M t) :
    Finset (BackboneCoordinate M t) :=
  Finset.univ.filter (fun e => u e.1 ∈ e.2.1)

/-- The interval of `s` consecutive starts in the cyclic index order.  The
bound proof is obtained from the supplied start index, so this definition has
no hidden nonempty-coordinate assumption. -/
def cyclicInterval {m : ℕ} (s : ℕ) (start : Fin m) : Finset (Fin m) :=
  (Finset.range s).image (fun a =>
    ⟨(start.val + a) % m, by
      apply Nat.mod_lt
      exact Nat.pos_of_ne_zero (by
        intro hm
        exact Fin.elim0 (hm ▸ start))⟩)

/-- The added coordinates containing a given backbone member. -/
def cyclicSupport {M t s : ℕ} (u : BackboneWord M t) :
    Finset (Fin (M ^ t)) :=
  Finset.univ.filter (fun k =>
    wordIndex u ∈ cyclicInterval s k)

/-- The actual augmented member: the complete-graph-dual backbone together
with its cyclic interval coordinates. -/
def augmentedMember {M t s : ℕ} (u : BackboneWord M t) :
    Finset (BackboneCoordinate M t ⊕ Fin (M ^ t)) :=
  (backboneMember u).image Sum.inl ∪
    (cyclicSupport (s := s) u).image Sum.inr

/-- The actual finite augmented family, obtained from all backbone words. -/
def augmentedFamily (M t s : ℕ) :
    Finset (Finset (BackboneCoordinate M t ⊕ Fin (M ^ t))) :=
  Finset.univ.image (augmentedMember (M := M) (t := t) (s := s))

 def backboneMemberCount (M t : ℕ) : ℕ := M ^ t

def backboneRank (M t : ℕ) : ℕ := (M - 1) * t

def augmentedRank (M t s : ℕ) : ℕ := backboneRank M t + s

/-- The agreement count of two actual product words. -/
def wordAgreementCount {M t : ℕ}
    (u v : BackboneWord M t) : ℕ :=
  (Finset.univ.filter (fun j : Fin t => u j = v j)).card

/-- The cyclic coordinates are disjoint precisely when the two actual members
have no common added coordinate. -/
def cyclicCoordinatesDisjoint {M t s : ℕ}
    (u v : BackboneWord M t) : Prop :=
  cyclicSupport (s := s) u ∩ cyclicSupport (s := s) v = ∅

/-- The support-layer coverage retained from the cyclic construction: each
member lies in `s` intervals and each interval contains `s` members. -/
def cyclicLayerCoverage (M t s : ℕ) : Prop :=
  (∀ u : BackboneWord M t,
    (cyclicSupport (s := s) u).card = s) ∧
  (∀ k : Fin (M ^ t),
    (Finset.univ.filter (fun u : BackboneWord M t =>
      k ∈ cyclicSupport (s := s) u)).card = s)

/-- The carrier and rank facts of the actual cyclic augmentation. -/
def cyclicConstructionFacts (M t s : ℕ) : Prop :=
  (augmentedFamily M t s).card = M ^ t ∧
    (∀ u : BackboneWord M t,
      (augmentedMember (s := s) u).card = augmentedRank M t s) ∧
    backboneRank M t = (M - 1) * t ∧
    augmentedRank M t s = (M - 1) * t + s ∧
    cyclicLayerCoverage M t s

/-- The full admissibility range of the cyclic construction. -/
def admissibleParameters (M t s : ℕ) : Prop :=
  7 ≤ M ∧ t < s ∧ s < 2 * t ∧ Nat.Prime s ∧
    Nat.Coprime s M ∧ 2 * s < M ^ t

/-- The random-shadow joint law for an actual finite uniform family. -/
def shadowJointProbability {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset (Finset α)) (r q : ℕ)
    (U T : Finset α) : ℝ :=
  if U ∈ F ∧ T ⊆ U ∧ T.card = q then
    1 / ((F.card : ℝ) * (Nat.choose r q : ℝ))
  else 0

def shadowMarginalU {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset (Finset α)) (U : Finset α) : ℝ :=
  if U ∈ F then 1 / (F.card : ℝ) else 0

def shadowMarginalT {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset (Finset α)) (r q : ℕ) (T : Finset α) : ℝ :=
  ∑ U : Finset α, shadowJointProbability F r q U T

/-- Natural-log mutual information of the actual random-shadow law. -/
def randomShadowMutualInformation
    {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset (Finset α)) (r q : ℕ) : ℝ :=
  ∑ U : Finset α, ∑ T : Finset α,
    let j := shadowJointProbability F r q U T
    if j = 0 then 0 else
      j * Real.log
        (j / (shadowMarginalU F U * shadowMarginalT F r q T))

/-- The information quantity used in the two target claims, evaluated on the
actual cyclic augmented family. -/
def cyclicInformation (M t s q : ℕ) : ℝ :=
  randomShadowMutualInformation
    (augmentedFamily M t s) (augmentedRank M t s) q

/-- Claim 36028: the actual complete-graph-dual product and cyclic layer have
the full agreement spectrum, actual augmented intersections, and the stated
proper linear-size intersection. -/
def claim36028 : Prop :=
  ∀ (M t s : ℕ),
    admissibleParameters M t s →
    cyclicConstructionFacts M t s ∧
    (∀ (u : BackboneWord M t) (a : ℕ), a < t →
      (Finset.univ.filter (fun v : BackboneWord M t =>
        wordAgreementCount u v = a)).card =
        Nat.choose t a * (M - 1) ^ (t - a) ∧
      Nat.choose t a * (M - 1) ^ (t - a) > 2 * (s - 1)) ∧
    (∀ (u : BackboneWord M t) (a : ℕ), a < t →
      ∃ v : BackboneWord M t,
        wordAgreementCount u v = a ∧
        cyclicCoordinatesDisjoint (s := s) u v ∧
        (augmentedMember (s := s) u ∩
          augmentedMember (s := s) v).card =
          t + a * (M - 2)) ∧
    (∀ a b : ℕ, a < t → b < t → a ≠ b →
      t + a * (M - 2) ≠ t + b * (M - 2)) ∧
    (∃ u v : BackboneWord M t,
      wordAgreementCount u v = t - 1 ∧
      u ≠ v ∧
      cyclicCoordinatesDisjoint (s := s) u v ∧
      (augmentedMember (s := s) u ∩
        augmentedMember (s := s) v).card =
        (M - 1) * t - (M - 2) ∧
      0 < (augmentedMember (s := s) u ∩
        augmentedMember (s := s) v).card ∧
      0 < ((augmentedMember (s := s) u ∩
        augmentedMember (s := s) v).card : ℝ) /
        (augmentedRank M t s : ℝ) ∧
      ∃ c : ℝ, 0 < c ∧
        c * (augmentedRank M t s : ℝ) ≤
          ((augmentedMember (s := s) u ∩
            augmentedMember (s := s) v).card : ℝ))

/-- A sequence of actual cyclic parameters is eventually in the admissible
prime interval, rather than asserting a prime for every parameter value. -/
def eventuallyAdmissible (M : ℕ) (s : ℕ → ℕ) : Prop :=
  ∀ᶠ t in Filter.atTop, admissibleParameters M t (s t)

/-- Claim 36029: on the actual cyclic augmented family, every positive shadow
order in range has the displayed lower bound eventually, and every positive
sublinear shadow sequence has information superlinear in its order. -/
def claim36029 : Prop :=
  ∀ (M : ℕ) (s : ℕ → ℕ),
    7 ≤ M → eventuallyAdmissible M s →
    (∀ᶠ t in Filter.atTop,
      cyclicConstructionFacts M t (s t) ∧
        augmentedRank M t (s t) = (M - 1) * t + s t ∧
        augmentedRank M t (s t) < (M + 1) * t) ∧
    (∀ q : ℕ, 1 ≤ q →
      ∀ᶠ t in Filter.atTop,
        admissibleParameters M t (s t) →
          q ≤ augmentedRank M t (s t) →
          cyclicInformation M t (s t) q ≥
            (1 / (M + 1 : ℝ)) *
              ((t : ℝ) * Real.log M - Real.log (2 * t))) ∧
    (∀ q : ℕ → ℕ,
      (∀ t, 1 ≤ q t ∧ q t ≤ augmentedRank M t (s t)) →
      Tendsto
        (fun t => (q t : ℝ) / (augmentedRank M t (s t) : ℝ))
        Filter.atTop (𝓝 0) →
      Tendsto
        (fun t => cyclicInformation M t (s t) (q t) /
          (q t : ℝ))
        Filter.atTop Filter.atTop) ∧
    (∀ C : ℝ, ∀ q : ℕ → ℕ,
      (∀ t, 1 ≤ q t ∧ q t ≤ augmentedRank M t (s t)) →
      Tendsto
        (fun t => (q t : ℝ) / (augmentedRank M t (s t) : ℝ))
        Filter.atTop (𝓝 0) →
      ∀ᶠ t in Filter.atTop,
        (q t : ℝ) * Real.log C <
          cyclicInformation M t (s t) (q t))

end
end MathlibPlus.Open.ResearchFormalization.R2071
