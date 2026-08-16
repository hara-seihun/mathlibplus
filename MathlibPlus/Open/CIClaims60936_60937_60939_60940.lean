import Mathlib

namespace MathlibPlus.Open.CIClaims60936_60937_60939_60940

/-- Adjacency for an ordinary undirected additive Cayley graph. -/
def additiveCayleyAdj {G : Type*} [AddGroup G] (S : Set G) (x y : G) : Prop :=
  x ≠ y ∧ y - x ∈ S

/-- Abstract graph isomorphism for the additive Cayley adjacency above. -/
def additiveCayleyGraphIso {G : Type*} [AddGroup G] (S T : Set G) : Prop :=
  ∃ e : G ≃ G, ∀ x y, additiveCayleyAdj S x y ↔ additiveCayleyAdj T (e x) (e y)

/-- Adjacency for a right-Cayley graph with edges `{x, x*s}`. -/
def rightCayleyAdj {G : Type*} [Group G] (S : Set G) (x y : G) : Prop :=
  x ≠ y ∧ x⁻¹ * y ∈ S

/-- Abstract graph isomorphism for the right-Cayley adjacency above. -/
def rightCayleyGraphIso {G : Type*} [Group G] (S T : Set G) : Prop :=
  ∃ e : G ≃ G, ∀ x y, rightCayleyAdj S x y ↔ rightCayleyAdj T (e x) (e y)

/-- The admitted valency/covalency fifteen CI claim on `C₄ × 𝔽₃³`. -/
def valencyFifteenCyclicFourTimesF3Cube : Prop :=
  let G := ZMod 4 × (Fin 3 → ZMod 3)
  ∀ (S T : Set G),
    S ⊆ ({0} : Set G)ᶜ →
    T ⊆ ({0} : Set G)ᶜ →
    (∀ ⦃x⦄, x ∈ S → -x ∈ S) →
    (∀ ⦃x⦄, x ∈ T → -x ∈ T) →
    min S.ncard (107 - S.ncard) = 15 →
    min T.ncard (107 - T.ncard) = 15 →
    additiveCayleyGraphIso S T →
    ∃ α : G ≃+ G, α '' S = T

/-- The admitted `C₇ × Q₁₂` valency-17/66 CI claim. -/
def quaternionTwelveCoprimeShellCI : Prop :=
  let G := Multiplicative (ZMod 7) × QuaternionGroup 3
  ∀ (S T : Set G),
    S ⊆ ({1} : Set G)ᶜ →
    T ⊆ ({1} : Set G)ᶜ →
    (∀ ⦃x⦄, x ∈ S → x⁻¹ ∈ S) →
    (∀ ⦃x⦄, x ∈ T → x⁻¹ ∈ T) →
    ((S.ncard = 17 ∧ T.ncard = 17) ∨ (S.ncard = 66 ∧ T.ncard = 66)) →
    rightCayleyGraphIso S T →
    ∃ α : G ≃* G, α '' S = T

/-- The admitted all-ranks binary-times-`C₉` CI claim with projection rank at most two. -/
def binaryTimesC9ProjectionRankAtMostTwo : Prop :=
  ∀ (r : ℕ),
    2 ≤ r →
    let G := (Fin r → ZMod 2) × ZMod 9
    ∀ (S : Set G),
      S ⊆ ({0} : Set G)ᶜ →
      (∀ ⦃x⦄, x ∈ S → -x ∈ S) →
      let U_S : Submodule (ZMod 2) (Fin r → ZMod 2) :=
        Submodule.span (ZMod 2) {x | ∃ z : ZMod 9, (x, z) ∈ S}
      Module.finrank (ZMod 2) U_S ≤ 2 →
      ∀ (T : Set G),
        T ⊆ ({0} : Set G)ᶜ →
        (∀ ⦃x⦄, x ∈ T → -x ∈ T) →
        additiveCayleyGraphIso S T →
        ∃ α : G ≃+ G, α '' S = T

/-- The admitted elementary-scalar outer-subgroup tripartite CI claim. -/
def elementaryScalarOuterSubgroupTripartiteCI : Prop :=
  ∀ (P : Finset {p : ℕ // Nat.Prime p})
    (V : ∀ p : P, Type)
    [vAdd : ∀ p : P, AddCommGroup (V p)]
    [vModule : ∀ p : P, Module (ZMod p.1.1) (V p)]
    [vFinite : ∀ p : P, Module.Finite (ZMod p.1.1) (V p)],
    let M := ∀ p : P, V p
    ∀ (omega : ∀ p : P, (ZMod p.1.1)ˣ),
      (∀ p : P, orderOf (omega p) = 3) →
      ∀ (theta : Multiplicative (ZMod 3) →* MulAut (Multiplicative M)),
        (∀ v : M,
          Multiplicative.toAdd
              ((theta (Multiplicative.ofAdd (1 : ZMod 3)))
                (Multiplicative.ofAdd v)) =
            fun p => (omega p : ZMod p.1.1) • v p) →
        ∀ (U : AddSubgroup M),
          let G := SemidirectProduct (Multiplicative M) (Multiplicative (ZMod 3)) theta
          let U_mul : Subgroup (Multiplicative M) := AddSubgroup.toSubgroup U
          let H : Subgroup G :=
            Subgroup.closure
              ((SemidirectProduct.inl (φ := theta)) '' (U_mul : Set (Multiplicative M)) ∪
                {SemidirectProduct.inr (φ := theta)
                  (Multiplicative.ofAdd (1 : ZMod 3))})
          let S_out : Set G :=
            (H : Set G) \ (SemidirectProduct.inl (φ := theta) '' (U_mul : Set (Multiplicative M)))
          let S_co : Set G := ((Set.univ : Set G) \ {1}) \ S_out
          ∀ (S : Set G),
            (S = S_out ∨ S = S_co) →
            ∀ (T : Set G),
              T ⊆ ({1} : Set G)ᶜ →
              (∀ ⦃x⦄, x ∈ T → x⁻¹ ∈ T) →
              rightCayleyGraphIso S T →
              ∃ α : G ≃* G, α '' S = T

end MathlibPlus.Open.CIClaims60936_60937_60939_60940
