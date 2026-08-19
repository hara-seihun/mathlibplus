import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R2785

abbrev BooleanBit35841 := ZMod 2

def normalizedTwoCocycle35841 {D : Type*} [Group D]
    (κ : D → D → BooleanBit35841) : Prop :=
  (∀ h : D, κ 1 h = 0 ∧ κ h 1 = 0) ∧
    ∀ h u v : D,
      κ h u + κ (h * u) v = κ u v + κ h (u * v)

def splitTwoCocycle35841 {D : Type*} [Group D]
    (κ : D → D → BooleanBit35841) : Prop :=
  ∃ s : D → BooleanBit35841,
    s 1 = 0 ∧
      ∀ h u : D, κ h u = s h + s u - s (h * u)

def nonsplitTwoCocycle35841 {D : Type*} [Group D]
    (κ : D → D → BooleanBit35841) : Prop :=
  normalizedTwoCocycle35841 κ ∧ ¬ splitTwoCocycle35841 κ

def booleanCharacter35841 {D : Type*} [Group D]
    (χ : D → BooleanBit35841) : Prop :=
  χ 1 = 0 ∧ ∀ h u : D, χ (h * u) = χ h + χ u

def switchSubgroupSet35841 {D : Type*} [Group D]
    (b : D → BooleanBit35841) : Set D :=
  {h | ∀ u : D, b (h * u) = b h + b u}

def relativeDerivative35841 {D : Type*} [Group D]
    (b : D → BooleanBit35841) (u : D)
    (x : D × BooleanBit35841) : D × BooleanBit35841 :=
  (x.1, x.2 + b (x.1 * u) + b x.1 + b u)

def derivativeRelation35841 {D : Type*} [Group D]
    (b : D → BooleanBit35841) (x y : D × BooleanBit35841) : Prop :=
  ∃ u : D, relativeDerivative35841 b u x = y

def derivativeOrbit35841 {D : Type*} [Group D]
    (b : D → BooleanBit35841) (x : D × BooleanBit35841) : Set (D × BooleanBit35841) :=
  {y | Relation.EqvGen (derivativeRelation35841 b) x y}

def centralPair35841 {D : Type*} [Group D]
    (h : D) : Set (D × BooleanBit35841) :=
  {(h, 0), (h, 1)}

def switchRelabel35841 {D : Type*} [Group D]
    (b : D → BooleanBit35841) : D × BooleanBit35841 → D × BooleanBit35841 :=
  fun x => (x.1, x.2 + b x.1)

def centralShear35841 {D : Type*} [Group D]
    (χ : D → BooleanBit35841) : D × BooleanBit35841 → D × BooleanBit35841 :=
  fun x => (x.1, x.2 + χ x.1)

/-- Claim 35841: a normalized switch and its extending central shear agree on
normal switch fibres, the other fibres are derivative central-pair orbits, and
both maps have the same image on every derivative orbit. -/
def claim35841 : Prop :=
  ∀ n : ℕ, n % 2 = 1 →
    ∀ (κ : DihedralGroup n → DihedralGroup n → BooleanBit35841)
      (b : DihedralGroup n → BooleanBit35841)
      (χ : DihedralGroup n → BooleanBit35841),
      nonsplitTwoCocycle35841 κ →
        b 1 = 0 →
          booleanCharacter35841 χ →
            (∀ h : DihedralGroup n,
              h ∈ switchSubgroupSet35841 b → χ h = b h) →
              (∀ h : DihedralGroup n,
                h ∈ switchSubgroupSet35841 b →
                  ∀ e : BooleanBit35841,
                    switchRelabel35841 b (h, e) =
                      centralShear35841 χ (h, e)) ∧
                (∀ h : DihedralGroup n,
                  h ∉ switchSubgroupSet35841 b →
                    ∃ u : DihedralGroup n,
                      relativeDerivative35841 b u (h, 0) = (h, 1)) ∧
                  (∀ h : DihedralGroup n,
                    h ∉ switchSubgroupSet35841 b →
                      centralPair35841 h = derivativeOrbit35841 b (h, 0)) ∧
                    (∀ h : DihedralGroup n,
                      switchRelabel35841 b '' centralPair35841 h =
                        centralPair35841 h) ∧
                      (∀ h : DihedralGroup n,
                        centralShear35841 χ '' centralPair35841 h =
                          centralPair35841 h) ∧
                        (∀ x : DihedralGroup n × BooleanBit35841,
                          switchRelabel35841 b '' derivativeOrbit35841 b x =
                            centralShear35841 χ '' derivativeOrbit35841 b x)

end MathlibPlus.Open.ResearchFormalization.R2785
