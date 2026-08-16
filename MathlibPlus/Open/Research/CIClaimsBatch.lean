import Mathlib

namespace MathlibPlus.Open.Research

/-- Claim 60143: the subgroup-difference sets in `C₂^r × C₉` are CI-sets. -/
def ciBinaryTimesC9 : Prop :=
  ∀ r : ℕ,
    let G := (Fin r → ZMod 2) × ZMod 9
    ∀ (K H : AddSubgroup G),
      K < H →
        let S : Set G := (H : Set G) \ (K : Set G)
        S ⊆ (Set.univ \ ({0} : Set G)) ∧
          (∀ x : G, x ∈ S → -x ∈ S) ∧
            ∀ T : Set G,
              T ⊆ (Set.univ \ ({0} : Set G)) →
                (∀ x : G, x ∈ T → -x ∈ T) →
                  (∃ e : G ≃ G,
                    ∀ x y : G, (y - x ∈ S ↔ e y - e x ∈ T)) →
                    ∃ α : G ≃+ G, Set.image α S = T

/-- Claim 60144: valency-five Cayley graphs on `C₇ × Q₁₂` are CI-graphs. -/
def ciCoprimeShellQ12 : Prop :=
  let Q12 := QuaternionGroup 3
  let G := Multiplicative (ZMod 7) × Q12
  ∀ S T : Set G,
    S ⊆ (Set.univ \ ({1} : Set G)) →
      T ⊆ (Set.univ \ ({1} : Set G)) →
        Set.ncard S = 5 →
          Set.ncard T = 5 →
            (∀ x : G, x ∈ S → x⁻¹ ∈ S) →
              (∀ x : G, x ∈ T → x⁻¹ ∈ T) →
                (∃ e : G ≃ G,
                  ∀ x y : G,
                    (x⁻¹ * y ∈ S ↔ (e x)⁻¹ * e y ∈ T)) →
                  ∃ α : G ≃* G, Set.image α S = T

/-- Claim 60146: disconnected Cayley graphs on the fixed-point-free scalar groups
`E(C_p,3)` are CI-graphs. -/
def ciScalarOrderThree : Prop :=
  ∀ (p : ℕ),
    Nat.Prime p →
      ∀ (omega : (ZMod p)ˣ),
        orderOf omega = 3 →
          let G := ZMod p × ZMod 3
          let scalar : ZMod 3 → (ZMod p)ˣ :=
            fun k => omega ^ k.val
          let mulE : G → G → G :=
            fun x y =>
              (x.1 + (scalar x.2 : ZMod p) * y.1, x.2 + y.2)
          let invE : G → G :=
            fun x =>
              (- ((omega⁻¹ ^ x.2.val : (ZMod p)ˣ) : ZMod p) * x.1, -x.2)
          let adj : Set G → G → G → Prop :=
            fun U x y => mulE (invE x) y ∈ U
          let connected : Set G → Prop :=
            fun U => ∀ x y : G, Relation.ReflTransGen (adj U) x y
          ∀ S T : Set G,
            S ⊆ (Set.univ \ ({(0, 0)} : Set G)) →
              T ⊆ (Set.univ \ ({(0, 0)} : Set G)) →
                (∀ x : G, x ∈ S → invE x ∈ S) →
                  (∀ x : G, x ∈ T → invE x ∈ T) →
                    (∃ e : G ≃ G,
                      ∀ x y : G, adj S x y ↔ adj T (e x) (e y)) →
                      ¬ connected S →
                        ∃ α : G ≃ G,
                          (∀ x y : G,
                            α (mulE x y) = mulE (α x) (α y)) ∧
                            Set.image α S = T

end MathlibPlus.Open.Research
