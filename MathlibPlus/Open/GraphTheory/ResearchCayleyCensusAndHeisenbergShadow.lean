import Mathlib

namespace MathlibPlus.Open.GraphTheory

noncomputable section

/-- Identity-free inverse-closed finite additive connection sets. -/
def researchAdditiveConnectionSet {G : Type*} [AddGroup G]
    (k : ℕ) (S : Finset G) : Prop :=
  (0 : G) ∉ S ∧
    (∀ x ∈ S, -x ∈ S) ∧
      S.card = k

/-- The graph-isomorphism relation for finite additive Cayley connection sets. -/
def researchAdditiveGraphIsomorphic {G : Type*} [AddGroup G]
    (S T : Finset G) : Prop :=
  Nonempty (SimpleGraph.addCayley (S : Set G) ≃g
    SimpleGraph.addCayley (T : Set G))

/-- The image of a finite connection set under an additive automorphism. -/
def researchAdditiveAutomorphismImage {G : Type*} [AddCommGroup G]
    [DecidableEq G] (α : G ≃+ G) (S : Finset G) : Finset G :=
  S.image α

/-- A complete representative family for additive-automorphism orbits. -/
def researchAdditiveAutOrbitRepresentatives
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (k c : ℕ) (R : Finset (Finset G)) : Prop :=
  R.card = c ∧
    (∀ S : Finset G, researchAdditiveConnectionSet k S →
      ∃ T ∈ R,
        researchAdditiveConnectionSet k T ∧
          ∃ α : G ≃+ G,
            researchAdditiveAutomorphismImage α S = T) ∧
    (∀ S ∈ R, researchAdditiveConnectionSet k S) ∧
    (∀ S ∈ R, ∀ T ∈ R,
      (∃ α : G ≃+ G,
        researchAdditiveAutomorphismImage α S = T) → S = T)

/-- A complete representative family for graph-isomorphism types. -/
def researchAdditiveGraphTypeRepresentatives
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (k c : ℕ) (R : Finset (Finset G)) : Prop :=
  R.card = c ∧
    (∀ S : Finset G, researchAdditiveConnectionSet k S →
      ∃ T ∈ R,
        researchAdditiveConnectionSet k T ∧
          researchAdditiveGraphIsomorphic S T) ∧
    (∀ S ∈ R, researchAdditiveConnectionSet k S) ∧
    (∀ S ∈ R, ∀ T ∈ R,
      researchAdditiveGraphIsomorphic S T → S = T)

/-- Singleton graph-isomorphism fibres over additive-automorphism orbits. -/
def researchAdditiveSingletonGraphFibres
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (k : ℕ) : Prop :=
  ∀ S T : Finset G,
    researchAdditiveConnectionSet k S →
    researchAdditiveConnectionSet k T →
    researchAdditiveGraphIsomorphic S T →
    ∃ α : G ≃+ G,
      researchAdditiveAutomorphismImage α S = T

/-- CI in a low band and its complementary high band. -/
def researchAdditiveCayleyCILowHigh
    (G : Type*) [AddCommGroup G] [Fintype G]
    (low high : ℕ) : Prop :=
  ∀ S T : Set G,
    (0 : G) ∉ S →
    (0 : G) ∉ T →
    (∀ x ∈ S, -x ∈ S) →
    (∀ x ∈ T, -x ∈ T) →
    (Set.ncard S ≤ low ∨ high ≤ Set.ncard S) →
    (Set.ncard T ≤ low ∨ high ≤ Set.ncard T) →
    Nonempty (SimpleGraph.addCayley S ≃g SimpleGraph.addCayley T) →
    ∃ α : G ≃+ G, α '' S = T

/-- Stabilizer relation between two one-point extensions of a parent. -/
def researchAdditiveStabilizerRelated
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (P S T : Finset G) : Prop :=
  ∃ α : G ≃+ G,
    researchAdditiveAutomorphismImage α P = P ∧
      researchAdditiveAutomorphismImage α S = T

/-- One extension from each setwise-stabilizer orbit of each parent. -/
def researchCanonicalAugmentationChildren
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (parents children : Finset (Finset G)) : Prop :=
  (∀ P ∈ parents,
    researchAdditiveConnectionSet 10 P →
      (∀ a : G, a ≠ -a → a ∉ P → -a ∉ P →
        ∃ C ∈ children, ∃ b : G,
          b ≠ -b ∧ b ∉ P ∧ -b ∉ P ∧
            C = insert b (insert (-b) P) ∧
            researchAdditiveStabilizerRelated P
              (insert a (insert (-a) P)) C) ∧
      (∀ C ∈ children,
        researchAdditiveConnectionSet 12 C ∧
          ∃ P ∈ parents, ∃ a : G,
            researchAdditiveConnectionSet 10 P ∧
              a ≠ -a ∧ a ∉ P ∧ -a ∉ P ∧
                C = insert a (insert (-a) P))) ∧
  (∀ P ∈ parents,
    researchAdditiveConnectionSet 10 P →
      ∀ C ∈ children, ∀ D ∈ children,
        (∃ a b : G,
          a ≠ -a ∧ b ≠ -b ∧ a ∉ P ∧ -a ∉ P ∧
            b ∉ P ∧ -b ∉ P ∧
            C = insert a (insert (-a) P) ∧
            D = insert b (insert (-b) P) ∧
            researchAdditiveStabilizerRelated P C D) → C = D)

/-- Exact C₃² × C₁₇ weight-six census and its low/high CI consequence. -/
def c3SquareCyclicSeventeenValencyTwelveCensus : Prop :=
  let G := (Fin 2 → ZMod 3) × ZMod 17
  Nat.card G = 153 ∧
    researchAdditiveCayleyCILowHigh G 12 140 ∧
    ∃ (parents children orbitRepresentatives graphRepresentatives :
        Finset (Finset ((Fin 2 → ZMod 3) × ZMod 17))),
      researchAdditiveAutOrbitRepresentatives 10 53724 parents ∧
      researchCanonicalAugmentationChildren parents children ∧
      children.card = 2414242 ∧
      researchAdditiveAutOrbitRepresentatives 12 596161
        orbitRepresentatives ∧
      researchAdditiveGraphTypeRepresentatives 12 596161
        graphRepresentatives ∧
      researchAdditiveSingletonGraphFibres (G := G) 12

/-- Exact low/high A₅ census on `C₂ × C₃⁴`, with no middle-valency claim. -/
def c2TimesC3FourthLowHighCensus : Prop :=
  let G := ZMod 2 × (Fin 4 → ZMod 3)
  Nat.card G = 162 ∧
    researchAdditiveCayleyCILowHigh G 10 151

/-- The cube subgroup `G^3 = V × 3C₉`, represented by `V × C₃`. -/
abbrev researchCubeKernel (V : Type*) := V × ZMod 3

def researchCubeKernelEmbedding {V : Type*}
    (h : researchCubeKernel V) : V × ZMod 9 :=
  (h.1, 3 * (h.2.val : ZMod 9))

/-- The orientation-preserving affine three-coset profile on `V × C₉`. -/
def binaryCyclicNineCubeCosetOrientedAffineProfilesHarmlessExact : Prop :=
  ∀ (V : Type*) [AddCommGroup V] [Fintype V],
    (∀ v : V, v + v = 0) →
    let G := V × ZMod 9
    let z : G := (0, 1)
    let H := researchCubeKernel V
    let n : H := (0, 1)
    ∀ (S T : Set G) (q : G ≃ G)
      (A : Fin 3 → H ≃+ H) (t : Fin 3 → H),
      q 0 = 0 →
      (0 : G) ∉ S →
      (0 : G) ∉ T →
      (∀ s : G, s ∈ S → -s ∈ S) →
      (∀ u : G, u ∈ T → -u ∈ T) →
      t 0 = 0 →
      (∀ i, A i n = n) →
      (∀ (i : Fin 3) (h : H),
        q (i.val • z + researchCubeKernelEmbedding h) =
          i.val • z + researchCubeKernelEmbedding (t i) +
            researchCubeKernelEmbedding (A i h)) →
      (∀ x y : G, y - x ∈ S ↔ q y - q x ∈ T) →
      ∃ α : G ≃+ G, α '' S = T

/-- The scalar vector and quotient factors for `E(C_p²,3)`. -/
abbrev researchScalarVector (p : ℕ) :=
  Multiplicative (ZMod p × ZMod p)
abbrev researchScalarC3 := Multiplicative (ZMod 3)
abbrev researchScalarHeisenberg (p : ℕ)
    (action : researchScalarC3 →*
      MulAut (researchScalarVector p)) :=
  researchScalarVector p ⋊[action] researchScalarC3

def researchScalarActionCondition (p : ℕ) (ω : ZMod p)
    (action : researchScalarC3 →*
      MulAut (researchScalarVector p)) : Prop :=
  ∀ v : researchScalarVector p,
    action (.ofAdd 1) v =
      .ofAdd (ω * v.toAdd.1, ω * v.toAdd.2)

def researchScalarPower (ω b : ZMod p) : Prop :=
  ∃ i : ZMod 3, b = ω ^ i.val

def researchHeisenbergQ (p : ℕ) [Fact (Nat.Prime p)] (ω : ZMod p)
    (action : researchScalarC3 →*
      MulAut (researchScalarVector p))
    (h : researchScalarHeisenberg p action) :
    researchScalarHeisenberg p action := by
  let v := Multiplicative.toAdd h.left
  let i := Multiplicative.toAdd h.right
  let a := ω ^ i.val
  exact ⟨
    Multiplicative.ofAdd
      (a * (v.2 + v.1 ^ 2 / (2 : ZMod p)), -a ^ 2 * v.1),
    Multiplicative.ofAdd (-i)⟩

def researchHeisenbergAlpha (p : ℕ) [Fact (Nat.Prime p)] (ω : ZMod p)
    (action : researchScalarC3 →*
      MulAut (researchScalarVector p))
    (h : researchScalarHeisenberg p action) :
    researchScalarHeisenberg p action := by
  let v := Multiplicative.toAdd h.left
  let i := Multiplicative.toAdd h.right
  exact ⟨Multiplicative.ofAdd ((1 + ω) * v.2, ω * v.1), h.right⟩

def researchHeisenbergD (p : ℕ) [Fact (Nat.Prime p)] (ω b t : ZMod p)
    (action : researchScalarC3 →*
      MulAut (researchScalarVector p))
    (h : researchScalarHeisenberg p action) :
    researchScalarHeisenberg p action := by
  let v := Multiplicative.toAdd h.left
  let i := Multiplicative.toAdd h.right
  let a := ω ^ i.val
  exact ⟨
    Multiplicative.ofAdd
      ((b⁻¹) ^ 2 * v.1 - b⁻¹ * v.2 * t +
        (1 - a) * t ^ 2 / (2 : ZMod p),
       (a - 1) * t + b⁻¹ * v.2),
    h.right⟩

def researchHeisenbergInverseClosed
    {p : ℕ} {action : researchScalarC3 →*
      MulAut (researchScalarVector p)}
    (U : Set (researchScalarHeisenberg p action)) : Prop :=
  ∀ h, h ∈ U ↔ h⁻¹ ∈ U

def researchHeisenbergDInvariant (p : ℕ) [Fact (Nat.Prime p)] (ω : ZMod p)
    (action : researchScalarC3 →*
      MulAut (researchScalarVector p))
    (U : Set (researchScalarHeisenberg p action)) : Prop :=
  ∀ b : ZMod p, researchScalarPower ω b →
    ∀ t : ZMod p, ∀ h,
      h ∈ U ↔ researchHeisenbergD p ω b t action h ∈ U

/-- The fixed-shadow statement on the explicitly displayed scalar group. -/
def researchHeisenbergFixedShadowAt (p : ℕ)
    [Fact (Nat.Prime p)] (ω : ZMod p) : Prop :=
  (∃ action : researchScalarC3 →*
      MulAut (researchScalarVector p),
    researchScalarActionCondition p ω action) ∧
    ∀ action : researchScalarC3 →*
        MulAut (researchScalarVector p),
      researchScalarActionCondition p ω action →
      let H := researchScalarHeisenberg p action
      Function.Bijective (researchHeisenbergQ p ω action) ∧
        researchHeisenbergQ p ω action 1 = 1 ∧
        ∀ U : Set H,
          researchHeisenbergInverseClosed U →
          researchHeisenbergDInvariant p ω action U →
          ∃ α : H ≃* H,
            (∀ h, α h = researchHeisenbergAlpha p ω action h) ∧
              ∀ h,
                researchHeisenbergQ p ω action h ∈ U ↔
                  α h ∈ U

/-- A concrete matrix description of the cubic upper-unitriangular pair. -/
abbrev researchGL3 (p : ℕ) :=
  Matrix.GeneralLinearGroup (Fin 3) (ZMod p)

def researchScalarMatrixPower (ω a : ZMod p) : Prop :=
  ∃ i : ZMod 3, a = ω ^ i.val

def researchXMatrix (a b x y z : ZMod p) :
    Matrix (Fin 3) (Fin 3) (ZMod p) :=
  !![a, x, z; 0, a * b, y; 0, 0, b]

def researchHMatrix (a x y : ZMod p) :
    Matrix (Fin 3) (Fin 3) (ZMod p) :=
  !![a, 0, x; 0, a, y; 0, 0, 1]

def researchKMatrix (b x z : ZMod p) :
    Matrix (Fin 3) (Fin 3) (ZMod p) :=
  !![1, x, z; 0, b, 0; 0, 0, b]

def researchDMatrix (p : ℕ) [Fact (Nat.Prime p)] (b t : ZMod p) :
    Matrix (Fin 3) (Fin 3) (ZMod p) :=
  !![b, b * t, b * t ^ 2 / (2 : ZMod p); 0, 1, t; 0, 0, b⁻¹]

def researchXSet (p : ℕ) (ω : ZMod p) : Set (researchGL3 p) :=
  {g | ∃ a b x y z : ZMod p,
    researchScalarMatrixPower ω a ∧ researchScalarMatrixPower ω b ∧
      (g : Matrix (Fin 3) (Fin 3) (ZMod p)) =
        researchXMatrix a b x y z}

def researchHSet (p : ℕ) (ω : ZMod p) : Set (researchGL3 p) :=
  {g | ∃ a x y : ZMod p,
    researchScalarMatrixPower ω a ∧
      (g : Matrix (Fin 3) (Fin 3) (ZMod p)) =
        researchHMatrix a x y}

def researchKSet (p : ℕ) (ω : ZMod p) : Set (researchGL3 p) :=
  {g | ∃ b x z : ZMod p,
    researchScalarMatrixPower ω b ∧
      (g : Matrix (Fin 3) (Fin 3) (ZMod p)) =
        researchKMatrix b x z}

def researchDSet (p : ℕ) [Fact (Nat.Prime p)] (ω : ZMod p) : Set (researchGL3 p) :=
  {g | ∃ b t : ZMod p,
    researchScalarMatrixPower ω b ∧
      (g : Matrix (Fin 3) (Fin 3) (ZMod p)) =
        researchDMatrix p b t}

def researchSetProduct {G : Type*} [Mul G]
    (A B : Set G) : Set G :=
  {x | ∃ a ∈ A, ∃ b ∈ B, a * b = x}

def researchSubgroupSet {G : Type*} [Group G]
    (A : Set G) : Prop :=
  1 ∈ A ∧
    (∀ a ∈ A, ∀ b ∈ A, a * b ∈ A) ∧
      (∀ a ∈ A, a⁻¹ ∈ A)

def researchUniqueFactorization {G : Type*} [Group G]
    (D A X : Set G) : Prop :=
  ∀ x ∈ X, ∃! pair : G × G,
    pair.1 ∈ D ∧ pair.2 ∈ A ∧ pair.1 * pair.2 = x

def researchCubicUpperUnitriangularPairData
    (p : ℕ) [Fact (Nat.Prime p)] (ω : ZMod p) : Prop :=
  let M := researchGL3 p
  let X := researchXSet p ω
  let H := researchHSet p ω
  let K := researchKSet p ω
  let D := researchDSet p ω
  researchSubgroupSet X ∧
    researchSubgroupSet H ∧
      researchSubgroupSet K ∧
        researchSubgroupSet D ∧
          Set.ncard X = 9 * p ^ 3 ∧
            Set.ncard D = 3 * p ∧
              Set.ncard H = 3 * p ^ 2 ∧
                Set.ncard K = 3 * p ^ 2 ∧
                  D ∩ H = ({1} : Set M) ∧
                    D ∩ K = ({1} : Set M) ∧
                      researchSetProduct D H = X ∧
                        researchSetProduct D K = X ∧
                          (∀ x ∈ X, ∀ h ∈ H,
                            x * h * x⁻¹ ∈ H) ∧
                            (∀ x ∈ X, ∀ k ∈ K,
                              x * k * x⁻¹ ∈ K) ∧
                              researchUniqueFactorization D H X ∧
                                researchUniqueFactorization D K X ∧
                                  H ≠ K ∧
                                    ¬ ∃ x : M, x ∈ X ∧
                                      (fun h => x * h * x⁻¹) '' H = K

/-- The explicit matrix regular pair and its labelled orbital fusion share
one fixed automorphism shadow. -/
def researchCubicRegularPairFixedShadow (p : ℕ)
    [Fact (Nat.Prime p)] (ω : ZMod p) : Prop :=
  researchCubicUpperUnitriangularPairData p ω ∧
    researchHeisenbergFixedShadowAt p ω

/-- Exact admitted order-three Heisenberg inverse-fusion shadow. -/
def orderThreeHeisenbergInverseFusionHasFixedAutomorphismShadow : Prop :=
  ∀ (p : ℕ), (hp : Nat.Prime p) → p % 3 = 1 →
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    ∀ ω : ZMod p, ω ^ 3 = 1 → ω ≠ 1 →
      researchCubicRegularPairFixedShadow p ω

end

end MathlibPlus.Open.GraphTheory
