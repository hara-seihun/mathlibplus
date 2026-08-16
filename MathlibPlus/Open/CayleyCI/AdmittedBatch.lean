import Mathlib

namespace MathlibPlus.Open.CayleyCI

private abbrev C2Pow (r : ℕ) := Fin r → ZMod 2

private def addCayleyGraph {G : Type*} [AddGroup G] (S : Set G) : SimpleGraph G :=
  SimpleGraph.fromRel (fun u v => v - u ∈ S)

private def rightCayleyGraph {G : Type*} [Group G] (S : Set G) : SimpleGraph G :=
  SimpleGraph.fromRel (fun u v => u⁻¹ * v ∈ S)

private abbrev C7 := Multiplicative (ZMod 7)
private abbrev Q12 := QuaternionGroup 3

noncomputable section

private def scale7 : ZMod 19 ≃+ ZMod 19 :=
  AddEquiv.ofBijective (AddMonoidHom.mulLeft (7 : ZMod 19)) (by decide)

private def sigma : MulAut (Multiplicative (ZMod 19)) := scale7.toMultiplicative

private def eAction : Multiplicative (ZMod 3) →* MulAut (Multiplicative (ZMod 19)) :=
  MonoidHom.mk' (fun k => sigma ^ (Multiplicative.toAdd k).val) (by
    intro k l
    fin_cases k <;> fin_cases l <;> decide)

private abbrev E19_3 :=
  SemidirectProduct (Multiplicative (ZMod 19)) (Multiplicative (ZMod 3)) eAction

end

/-- The admitted `C₂^r × C₉` ordinary undirected CI assertion. -/
def claim60121 : Prop :=
  ∀ r : ℕ, 2 ≤ r →
    ∀ (x y : C2Pow r),
      LinearIndependent (ZMod 2) ![x, y] →
      ∀ c : ZMod 9, addOrderOf c = 9 →
        let S : Set (C2Pow r × ZMod 9) :=
          {(x, 0), (y, 0), (0, c), (0, -c)}
        ∀ T : Set (C2Pow r × ZMod 9),
          T ⊆ (Set.univ \ {0}) →
          (∀ t ∈ T, -t ∈ T) →
          Nonempty (addCayleyGraph S ≃g addCayleyGraph T) →
          ∃ α : (C2Pow r × ZMod 9) ≃+ (C2Pow r × ZMod 9),
            α '' S = T

/-- The admitted `E(C₁₉,3)` ordinary undirected CI assertion. -/
def claim60123 : Prop :=
  ∀ S T : Set E19_3,
    S ⊆ (Set.univ \ {1}) →
    (∀ s ∈ S, s⁻¹ ∈ S) →
    T ⊆ (Set.univ \ {1}) →
    (∀ t ∈ T, t⁻¹ ∈ T) →
    Nonempty (rightCayleyGraph S ≃g rightCayleyGraph T) →
    ∃ α : E19_3 ≃* E19_3, α '' S = T

/-- The admitted valency-at-most-four `C₇ × Q₁₂` CI assertion. -/
def claim60124 : Prop :=
  ∀ S T : Set (C7 × Q12),
    S ⊆ (Set.univ \ {1}) →
    (∀ s ∈ S, s⁻¹ ∈ S) →
    S.ncard ≤ 4 →
    T ⊆ (Set.univ \ {1}) →
    (∀ t ∈ T, t⁻¹ ∈ T) →
    T.ncard ≤ 4 →
    Nonempty (rightCayleyGraph S ≃g rightCayleyGraph T) →
    ∃ α : (C7 × Q12) ≃* (C7 × Q12), α '' S = T

end MathlibPlus.Open.CayleyCI
