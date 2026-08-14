import Mathlib

namespace MathlibPlus.Open.Combinatorics

abbrev RankThreeField (p : ℕ) := ZMod p
abbrev RankThreeVector (p : ℕ) := RankThreeField p × RankThreeField p

/-- The base semidirect-product carrier `F ⋊ C3`. -/
structure RankThreeBase (p : ℕ) where
  v : RankThreeField p
  k : ZMod 3

/-- The carrier `(F ⊕ W) ⋊ C3` with `W = F²`. -/
structure RankThreeGroup (p : ℕ) where
  v : RankThreeField p
  w : RankThreeVector p
  k : ZMod 3

/-- The scalar `ω^k` for `k ∈ C3`. -/
def rankThreeOmegaPow {p : ℕ} (ω : RankThreeField p) (k : ZMod 3) : RankThreeField p :=
  ω ^ k.val

/-- The displayed multiplication on `G`. -/
def rankThreeMul {p : ℕ} (ω : RankThreeField p) :
    RankThreeGroup p → RankThreeGroup p → RankThreeGroup p
  | x, y =>
      { v := x.v + rankThreeOmegaPow ω x.k * y.v
        w := x.w + rankThreeOmegaPow ω x.k • y.w
        k := x.k + y.k }

/-- Inverse for the displayed semidirect-product multiplication. -/
def rankThreeInv {p : ℕ} (ω : RankThreeField p) :
    RankThreeGroup p → RankThreeGroup p
  | x =>
      { v := -(rankThreeOmegaPow ω (-x.k) * x.v)
        w := -(rankThreeOmegaPow ω (-x.k) • x.w)
        k := -x.k }

/-- The normalized vertical shear `q`. -/
def normalizedVerticalShear {p : ℕ}
    (h : ZMod 3 → RankThreeField p → RankThreeVector p) :
    RankThreeGroup p → RankThreeGroup p
  | x =>
      { v := x.v
        w := x.w + h x.k x.v
        k := x.k }

/-- The defect `D_(u,l)(v,k)` from the packet. -/
def rankThreeDefect {p : ℕ} (ω : RankThreeField p)
    (h : ZMod 3 → RankThreeField p → RankThreeVector p)
    (a b : RankThreeBase p) : RankThreeVector p :=
  rankThreeOmegaPow ω (-a.k) •
      (h (a.k + b.k) (a.v + rankThreeOmegaPow ω a.k * b.v) -
        h a.k a.v) -
    h b.k b.v

/-- The span defining `H_(v,k)`. -/
def rankThreeH {p : ℕ} (ω : RankThreeField p)
    (h : ZMod 3 → RankThreeField p → RankThreeVector p)
    (b : RankThreeBase p) :
    Submodule (RankThreeField p) (RankThreeVector p) :=
  Submodule.span (RankThreeField p)
    (Set.range (fun a : RankThreeBase p => rankThreeDefect ω h a b))

/-- The set `K` of base points with zero defect span. -/
def rankThreeK {p : ℕ} (ω : RankThreeField p)
    (h : ZMod 3 → RankThreeField p → RankThreeVector p) : Set (RankThreeBase p) :=
  {b | rankThreeH ω h b = ⊥}

/-- The displayed difference operation `x⁻¹ y`. -/
def rankThreeDiff {p : ℕ} (ω : RankThreeField p)
    (x y : RankThreeGroup p) : RankThreeGroup p :=
  rankThreeMul ω (rankThreeInv ω x) y

/-- Inverse-closedness of a connection set for the displayed group law. -/
def rankThreeInverseClosed {p : ℕ} (ω : RankThreeField p)
    (T : Set (RankThreeGroup p)) : Prop :=
  ∀ x, x ∈ T ↔ rankThreeInv ω x ∈ T

/-- Connectedness of the Cayley graph for the displayed difference relation. -/
def rankThreeCayleyConnected {p : ℕ} (ω : RankThreeField p)
    (T : Set (RankThreeGroup p)) : Prop :=
  ∀ x y, Relation.ReflTransGen
      (fun a b : RankThreeGroup p => rankThreeDiff ω a b ∈ T) x y

/-- A bijective homomorphism for the displayed group multiplication. -/
def rankThreeAutomorphism {p : ℕ} (ω : RankThreeField p)
    (α : RankThreeGroup p ≃ RankThreeGroup p) : Prop :=
  ∀ x y,
    α (rankThreeMul ω x y) = rankThreeMul ω (α x) (α y)

/-- The normalized rank-three vertical-shear witness relation. -/
def normalizedRankThreeWitness {p : ℕ}
    (ω : RankThreeField p)
    (h : ZMod 3 → RankThreeField p → RankThreeVector p)
    (S T : Set (RankThreeGroup p)) : Prop :=
  rankThreeInverseClosed ω T ∧
    rankThreeCayleyConnected ω T ∧
    (∀ x y,
      rankThreeDiff ω x y ∈ S ↔
        rankThreeDiff ω (normalizedVerticalShear h x)
          (normalizedVerticalShear h y) ∈ T)

/-- Rank-three low-valency CI conclusion and its valency threshold. -/
def rankThreeLowSylowThreshold_claim59838 : Prop :=
  ∀ (p : ℕ), Nat.Prime p →
    ∀ (ω : RankThreeField p), ω ^ 3 = 1 → ω ≠ 1 →
      ∀ (h : ZMod 3 → RankThreeField p → RankThreeVector p),
        h 0 0 = 0 →
          ∃ α : RankThreeGroup p ≃ RankThreeGroup p,
            rankThreeAutomorphism ω α ∧
            (∀ (S T : Set (RankThreeGroup p)),
              normalizedRankThreeWitness ω h S T →
                Set.ncard T < 4 * p →
                  (∃ b : RankThreeBase p,
                    b ∈ rankThreeK ω h ∧ b ≠ { v := 0, k := 0 }) ∧
                    α '' S = T) ∧
            (∀ (S T : Set (RankThreeGroup p)),
              normalizedRankThreeWitness ω h S T →
                (¬ ∃ β : RankThreeGroup p ≃ RankThreeGroup p,
                    rankThreeAutomorphism ω β ∧ β '' S = T) →
                  4 * p ≤ Set.ncard T)

end MathlibPlus.Open.Combinatorics
