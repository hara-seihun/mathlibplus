import Mathlib

<<<<<<< ours

namespace MathlibPlus.Open.ResearchFormalizationBatch

abbrev Vec (p r : ℕ) := Fin r → ZMod p

/-- An inverse-pair atom, represented by the unordered pair `{h,-h}`. -/
def InversePairAtom (p r : ℕ) :=
  {s : Finset (Vec p r) // ∃ h : Vec p r, h ≠ 0 ∧ s = ({h, -h} : Finset (Vec p r))}

def connectionSet (C : Finset (InversePairAtom p r)) : Set (Vec p r) := by
  classical
  exact {h | ∃ u ∈ C, h ∈ u.1}

def edgeAtom (u : InversePairAtom p r) : Set (Finset (Vec p r)) :=
  {e | ∃ h ∈ u.1, ∃ x : Vec p r, e = ({x, x + h} : Finset (Vec p r))}

def edgeSet (C : Finset (InversePairAtom p r)) : Set (Finset (Vec p r)) := by
  classical
  exact {e | ∃ u ∈ C, e ∈ edgeAtom u}

def mapAtom (L : Vec p r ≃ₗ[ZMod p] Vec p r) (u : InversePairAtom p r) :
    InversePairAtom p r :=
  ⟨u.1.image L, by
    rcases u.2 with ⟨h, hh, hu⟩
    refine ⟨L h, ?_, ?_⟩
    · intro hz
      apply hh
      apply L.injective
      simpa using hz
    · rw [hu]
      ext x
      simp⟩

noncomputable def mapAtoms (L : Vec p r ≃ₗ[ZMod p] Vec p r)
    (C : Finset (InversePairAtom p r)) : Finset (InversePairAtom p r) := by
  classical
  exact C.image (mapAtom L)

def mapEdges (f : Vec p r ≃ Vec p r) (E : Set (Finset (Vec p r))) :
    Set (Finset (Vec p r)) := by
  classical
  exact {e | ∃ d ∈ E, e = d.image f}

noncomputable def atomRank (p r : ℕ) (hp : Nat.Prime p)
    (s : Finset (InversePairAtom p r)) : ℕ := by
  classical
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  exact Module.finrank (ZMod p)
    (Submodule.span (ZMod p)
      {v : Vec p r | ∃ u ∈ s, v ∈ u.1})

def SameVectorMatroidProfile (p r : ℕ) (hp : Nat.Prime p)
    (C C' : Finset (InversePairAtom p r)) : Prop := by
  classical
  exact ∃ e : {u // u ∈ C} ≃ {u // u ∈ C'},
    ∀ s : Finset {u // u ∈ C},
      atomRank p r hp (s.image (fun u => u.1)) =
        atomRank p r hp (s.image (fun u => (e u).1))

def GLPreservesCompleteRankProfile : Prop :=
  ∀ (p r : ℕ) (hp : Nat.Prime p), p % 2 = 1 →
    ∀ C : Finset (InversePairAtom p r),
      ∀ L : Vec p r ≃ₗ[ZMod p] Vec p r,
        SameVectorMatroidProfile p r hp C (mapAtoms L C)


def GraphIso (S S' : Set (Vec p r)) (f : Vec p r ≃ Vec p r) : Prop :=
  ∀ x y, (y - x ∈ S) ↔ (f y - f x ∈ S')

def ZeroFixingGraphIso (S S' : Set (Vec p r)) (f : Vec p r ≃ Vec p r) : Prop :=
  f 0 = 0 ∧ GraphIso S S' f

def CayleyGraphIsomorphic (S S' : Set (Vec p r)) : Prop :=
  ∃ f : Vec p r ≃ Vec p r, GraphIso S S' f

def MapsConnectionSet (L : Vec p r ≃ₗ[ZMod p] Vec p r)
    (S S' : Set (Vec p r)) : Prop :=
  ∀ h, h ∈ S ↔ L h ∈ S'

/-- The exact inverse-pair matroid defect implication. -/
def ExactInversePairMatroidDefectGate : Prop :=
  ∀ (p r : ℕ) (hp : Nat.Prime p), p % 2 = 1 →
    ∀ (C C' : Finset (InversePairAtom p r))
      (f : Vec p r ≃ Vec p r),
      ZeroFixingGraphIso (connectionSet C) (connectionSet C') f →
      mapEdges f (edgeSet C) = edgeSet C' →
      ¬ SameVectorMatroidProfile p r hp C C' →
      CayleyGraphIsomorphic (connectionSet C) (connectionSet C') ∧
        ¬ ∃ L : Vec p r ≃ₗ[ZMod p] Vec p r,
          MapsConnectionSet L (connectionSet C) (connectionSet C')

end MathlibPlus.Open.ResearchFormalizationBatch


namespace MathlibPlus.Open.ResearchFormalizationBatch

abbrev Q12 := ZMod 6 × ZMod 2
abbrev C7Q12 := ZMod 7 × Q12

def q12Mul (u v : Q12) : Q12 :=
  (u.1 + (if u.2 = 0 then v.1 else -v.1) +
      (if u.2 = 1 ∧ v.2 = 1 then 3 else 0),
    u.2 + v.2)

def q12One : Q12 := (0, 0)

def q12z : Q12 := (3, 0)

def q12Inv (u : Q12) : Q12 :=
  if u.2 = 0 then (-u.1, 0) else (u.1 + 3, 1)

def q12T : Set Q12 := {(1, 0), (2, 0), (4, 0), (5, 0)}

def gMul (u v : C7Q12) : C7Q12 :=
  (u.1 + v.1, q12Mul u.2 v.2)

def gOne : C7Q12 := (0, q12One)

def gInv (u : C7Q12) : C7Q12 :=
  (-(u.1), q12Inv u.2)

def gConnectionSet : Set C7Q12 :=
  ((Set.univ : Set (ZMod 7)) \ {0}) ×ˢ (Set.univ : Set Q12) ∪
    ({0} ×ˢ q12T)

def q12Adj (u v : Q12) : Prop :=
  u ≠ v ∧ ∃ t ∈ q12T, v = q12Mul u t

def gAdj (u v : C7Q12) : Prop :=
  u ≠ v ∧ ∃ s ∈ gConnectionSet, v = gMul u s

def graphAutomorphismSet {α : Type} (adj : α → α → Prop) : Set (Equiv.Perm α) :=
  {f | ∀ x y, adj x y ↔ adj (f x) (f y)}

def fibreWreathSet (localAut : Set (Equiv.Perm Q12)) : Set (Equiv.Perm C7Q12) :=
  {f | ∃ σ : Equiv.Perm (ZMod 7),
    ∀ a : ZMod 7, ∃ g : Equiv.Perm Q12, g ∈ localAut ∧
      ∀ h : Q12, f (a, h) = (σ a, g h)}

def complementAdj (u v : C7Q12) : Prop :=
  u ≠ v ∧ ¬ gAdj u v

def q12DicyclicLaw : Prop :=
  (∀ a b c : Q12, q12Mul (q12Mul a b) c = q12Mul a (q12Mul b c)) ∧
  (∀ a : Q12, q12Mul q12One a = a ∧ q12Mul a q12One = a) ∧
  (∀ a : Q12, q12Mul a (q12Inv a) = q12One ∧
    q12Mul (q12Inv a) a = q12One)

def c7Q12GroupLaw : Prop :=
  (∀ a b c : C7Q12, gMul (gMul a b) c = gMul a (gMul b c)) ∧
  (∀ a : C7Q12, gMul gOne a = a ∧ gMul a gOne = a) ∧
  (∀ a : C7Q12, gMul a (gInv a) = gOne ∧ gMul (gInv a) a = gOne)

def q12CayleyAutomorphismSet : Set (Equiv.Perm Q12) :=
  graphAutomorphismSet q12Adj

def C7Q12GraphClaim : Prop :=
  q12DicyclicLaw ∧
  c7Q12GroupLaw ∧
  (∀ t ∈ q12T, q12Inv t ∈ q12T) ∧
  (∀ s ∈ gConnectionSet, gInv s ∈ gConnectionSet) ∧
  Nat.card C7Q12 = 84 ∧
  (∀ x : C7Q12, Nat.card {y : C7Q12 // gAdj x y} = 76) ∧
  (∀ a : ZMod 7, ∀ h k : Q12,
    Relation.ReflTransGen complementAdj (a, h) (a, k)) ∧
  (∀ a b : ZMod 7, a ≠ b → ∀ h k : Q12,
    ¬ Relation.ReflTransGen complementAdj (a, h) (b, k)) ∧
  graphAutomorphismSet gAdj = fibreWreathSet q12CayleyAutomorphismSet ∧
  fibreWreathSet q12CayleyAutomorphismSet ⊂
    fibreWreathSet (Set.univ : Set (Equiv.Perm Q12))

end MathlibPlus.Open.ResearchFormalizationBatch


namespace MathlibPlus.Open.ResearchFormalizationBatch

/-- The finite coefficient carrier for positive Dirichlet polynomials supported in `n ≤ N`. -/
def FiniteDirichletCarrier (N : ℕ) :=
  {a : ℕ → ℂ // a 0 = 0 ∧ ∀ n, N < n → a n = 0}

noncomputable def literalPhaseCarrier (x : ℝ) (n : ℕ) : ℂ :=
  if n = 0 then 0
  else Complex.exp ((-Complex.I * (x / 2 : ℝ)) * Real.log (n : ℝ))

noncomputable def dirichletTerm (N : ℕ) (t σ x : ℝ) (n : ℕ) : ℂ :=
  if 1 ≤ n ∧ n ≤ N then
    Complex.exp (((t / 4) * (Real.log (n : ℝ)) ^ 2 : ℝ)) *
      Complex.exp ((((-σ : ℂ) - Complex.I * (x / 2 : ℝ)) *
        (Real.log (n : ℝ) : ℂ)))
  else 0

noncomputable def finiteDirichletSum (N : ℕ) (t σ x : ℝ) : FiniteDirichletCarrier N := by
  refine ⟨dirichletTerm N t σ x, ?_⟩
  constructor
  · simp [dirichletTerm]
  · intro n hn
    simp [dirichletTerm, hn]

/-- The literal `n^(-ix/2)` factor is retained as an exponential carrier. -/
def LiteralFiniteDirichletCarrierClaim : Prop :=
  let L : ℝ := 1529 / 10000
  let t : ℝ := 1899 / 10000
  let N0 : ℕ := 690988
  let N : ℕ := 690989
  let σ : ℝ := 1 / 2 + (L / 2) * Real.log (N0 : ℝ) - 1 / 1000
  ∀ x : ℝ,
    let Sx := finiteDirichletSum N t σ x
    (∀ n : ℕ, 1 ≤ n → n ≤ N →
      Sx.1 n =
        Complex.exp (((t / 4) * (Real.log (n : ℝ)) ^ 2 : ℝ)) *
          Complex.exp ((((-σ : ℂ) - Complex.I * (x / 2 : ℝ)) *
            (Real.log (n : ℝ) : ℂ)))) ∧
    (∀ n : ℕ, 1 ≤ n → n ≤ N →
      literalPhaseCarrier x n =
        Complex.exp ((-Complex.I * (x / 2 : ℝ)) *
          (Real.log (n : ℝ) : ℂ)))

end MathlibPlus.Open.ResearchFormalizationBatch


namespace MathlibPlus.Open.ResearchFormalizationBatch

abbrev BinaryBlockVector := Fin 2 → ZMod 2
abbrev ThreeBlockVector := Fin 3 → BinaryBlockVector

def tripleRelationModule : Submodule (ZMod 2) ThreeBlockVector :=
  Submodule.span (ZMod 2)
    {v : ThreeBlockVector |
      v 0 0 = v 1 0 ∧ v 1 0 = v 2 0}

def supportedOnTwoBlocks (v : ThreeBlockVector) : Prop :=
  ∃ i j : Fin 3, i ≠ j ∧
    ∀ k : Fin 3, k ≠ i → k ≠ j → v k = 0

def pairwiseShadowSpan : Submodule (ZMod 2) ThreeBlockVector :=
  Submodule.span (ZMod 2)
    {v : ThreeBlockVector | v ∈ tripleRelationModule ∧ supportedOnTwoBlocks v}

def genuineThreeCoordinateRelation : ThreeBlockVector :=
  fun _ j => if j = 0 then 1 else 0

/-- Pairwise-supported relation vectors do not generate the displayed
three-coordinate relation. -/
def PairwiseGoursatShadowObstruction : Prop :=
  (∀ v : ThreeBlockVector,
    v ∈ tripleRelationModule ↔
      (v 0 0 = v 1 0 ∧ v 1 0 = v 2 0)) ∧
  pairwiseShadowSpan ≠ tripleRelationModule ∧
  genuineThreeCoordinateRelation ∈ tripleRelationModule ∧
  genuineThreeCoordinateRelation ∉ pairwiseShadowSpan

end MathlibPlus.Open.ResearchFormalizationBatch
=======
namespace MathlibPlus.Open.ResearchFormalization.Batch_01a000fb

/-! Exact open statements from the admitted formalization packet. -/

section RationalKernelCone

/-- The support of a rational coordinate vector. -/
def rationalSupport {l : ℕ} (v : Fin l → ℚ) : Finset (Fin l) :=
  Finset.univ.filter (fun i => v i ≠ 0)

/-- `K_L = ker(L) ∩ ℚ_{≥0}^l`. -/
def rationalKernelCone
    {l n : ℕ}
    (L : (Fin l → ℚ) →ₗ[ℚ] (Fin n → ℚ))
    (p : Fin l → ℚ) : Prop :=
  L p = 0 ∧ ∀ i : Fin l, 0 ≤ p i

/-- Support-minimality in the sense used by the admitted claim. -/
def supportMinimalKernelRay
    {l n : ℕ}
    (L : (Fin l → ℚ) →ₗ[ℚ] (Fin n → ℚ))
    (q : Fin l → ℚ) : Prop :=
  q ≠ 0 ∧ rationalKernelCone L q ∧
    ∀ r : Fin l → ℚ,
      rationalKernelCone L r →
      r ≠ 0 →
      rationalSupport r ⊆ rationalSupport q →
      rationalSupport r ≠ rationalSupport q →
      False

/-- R-4881.2: rational nonnegative kernel-cone decomposition. -/
def claim53613
    {l n : ℕ}
    (L : (Fin l → ℚ) →ₗ[ℚ] (Fin n → ℚ)) : Prop :=
  ∀ p : Fin l → ℚ,
    rationalKernelCone L p →
    p ≠ 0 →
    ∃ k : ℕ,
      ∃ α : Fin k → ℚ,
      ∃ q : Fin k → (Fin l → ℚ),
        (∀ i : Fin k, 0 ≤ α i) ∧
        (∀ i : Fin k, supportMinimalKernelRay L (q i)) ∧
        (∀ i : Fin k, rationalSupport (q i) ⊆ rationalSupport p) ∧
        p = ∑ i : Fin k, α i • q i

end RationalKernelCone

section QuotientParityCounterexample

/-- R-5065.S6: the explicit two-dimensional quotient-parity counterexample. -/
def claim53621 : Prop :=
  let Δ : Submodule ℚ (ℚ × ℚ) :=
    Submodule.span ℚ ({(1, 1)} : Set (ℚ × ℚ))
  let Qplus : ℚ × ℚ := (1, 0)
  let Qminus : ℚ × ℚ := (0, 1)
  Qplus + Qminus ∈ Δ ∧
    Qminus ≠ -Qplus ∧
    Submodule.Quotient.mk (p := Δ) Qminus =
      -Submodule.Quotient.mk (p := Δ) Qplus ∧
    Submodule.Quotient.mk (p := Δ) (Qplus + Qminus) = 0

end QuotientParityCounterexample

section CharacteristicCyclicSection

/-- The coordinate multiplication displayed in R-4714.1.  The `val` of the
`ZMod 8` coordinate is used for the parity exponent. -/
def coordinateMul (m : ℕ) (u v : ZMod m × ZMod 8) : ZMod m × ZMod 8 :=
  (u.1 + (-1 : ZMod m) ^ u.2.val * v.1, u.2 + v.2)

def coordinateOne (m : ℕ) : ZMod m × ZMod 8 := (0, 0)

def coordinatePow {m : ℕ} (g : ZMod m × ZMod 8) : ℕ → ZMod m × ZMod 8
  | 0 => coordinateOne m
  | n + 1 => coordinateMul m (coordinatePow g n) g

/-- The concrete characteristic section in the displayed coordinates. -/
def characteristicSection (m : ℕ) : Set (ZMod m × ZMod 8) :=
  {u | u.2 ∈ ({0, 2, 4, 6} : Set (ZMod 8))}

def coordinateGroupAxioms (m : ℕ) : Prop :=
  (∀ x y z, coordinateMul m (coordinateMul m x y) z =
    coordinateMul m x (coordinateMul m y z)) ∧
  (∀ x, coordinateMul m (coordinateOne m) x = x ∧
    coordinateMul m x (coordinateOne m) = x) ∧
  (∀ x, ∃ y,
    coordinateMul m x y = coordinateOne m ∧
      coordinateMul m y x = coordinateOne m)

def coordinateSubgroup (m : ℕ) (S : Set (ZMod m × ZMod 8)) : Prop :=
  coordinateOne m ∈ S ∧
    (∀ x ∈ S, ∀ y ∈ S, coordinateMul m x y ∈ S) ∧
    (∀ x ∈ S, ∃ y ∈ S,
      coordinateMul m x y = coordinateOne m ∧
        coordinateMul m y x = coordinateOne m)

def coordinateA (m : ℕ) : ZMod m × ZMod 8 := (1, 0)

def coordinateB (m : ℕ) : ZMod m × ZMod 8 := (0, 1)

def coordinateGeneratedSubgroup
    (m : ℕ) (S : Set (ZMod m × ZMod 8)) : Set (ZMod m × ZMod 8) :=
  {x | ∀ T : Set (ZMod m × ZMod 8),
    coordinateSubgroup m T → S ⊆ T → x ∈ T}

def coordinateCyclic (m : ℕ) (S : Set (ZMod m × ZMod 8)) : Prop :=
  ∃ g ∈ S, ∀ x ∈ S, ∃ n : ℕ, coordinatePow g n = x

def coordinateAutomorphism (m : ℕ) (f : (ZMod m × ZMod 8) → (ZMod m × ZMod 8)) : Prop :=
  Function.Bijective f ∧
    f (coordinateOne m) = coordinateOne m ∧
    ∀ x y, f (coordinateMul m x y) =
      coordinateMul m (f x) (f y)

/-- R-4714.1: the coordinate group and its characteristic cyclic section. -/
def claim53571 : Prop :=
  ∀ m : ℕ, Odd m → 1 < m →
    coordinateGroupAxioms m ∧
      characteristicSection m =
        coordinateGeneratedSubgroup m
          ({coordinateA m, coordinateMul m (coordinateB m) (coordinateB m)} :
            Set (ZMod m × ZMod 8)) ∧
      coordinateSubgroup m (characteristicSection m) ∧
      coordinateCyclic m (characteristicSection m) ∧
      (∀ f, coordinateAutomorphism m f →
        ∀ x, x ∈ characteristicSection m ↔
          f x ∈ characteristicSection m) ∧
      (∃ x, x ∈ characteristicSection m) ∧
      (∃ x, x ∉ characteristicSection m) ∧
      (∃ x y, x ∈ characteristicSection m ∧
        y ∈ characteristicSection m ∧ x ≠ y) ∧
      Nat.card {x : ZMod m × ZMod 8 //
        x ∈ characteristicSection m} = 4 * m

end CharacteristicCyclicSection

end MathlibPlus.Open.ResearchFormalization.Batch_01a000fb
>>>>>>> theirs
