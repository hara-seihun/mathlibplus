import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch01Worker01a000eb

/-!
This file contains statement-only formalizations.  The declarations below are
intentionally propositions rather than proofs: they are the exact open claims
represented by the corresponding admitted packet entries.
-/

/-- The affine permutation model on the eight points of `AGL(3,2)`. -/
abbrev AffineThreeTwo := Fin 3 → ZMod 2

def affinePermutation (A : AffineThreeTwo ≃+ AffineThreeTwo)
    (b : AffineThreeTwo) : Equiv.Perm AffineThreeTwo :=
  A.toEquiv.trans (Equiv.addRight b)

def AGLThreeTwo : Subgroup (Equiv.Perm AffineThreeTwo) :=
  Subgroup.closure
    {p | ∃ (A : AffineThreeTwo ≃+ AffineThreeTwo) (b : AffineThreeTwo),
      p = affinePermutation A b}

def IsRegularPermutationSubgroup
    (Q : Subgroup (Equiv.Perm AffineThreeTwo)) : Prop :=
  ∀ x y : AffineThreeTwo, ∃! q : Q, q.1 x = y

def IsRegularQuaternionSubgroup
    (Q : Subgroup (Equiv.Perm AffineThreeTwo)) : Prop :=
  Q ≤ AGLThreeTwo ∧
    Nat.card Q = 8 ∧
    Nonempty (Q ≃* QuaternionGroup 2) ∧
    IsRegularPermutationSubgroup Q

/-- Claim 38306: the exact regular-`Q₈` census and its ordered-pair count. -/
def claim38306 : Prop :=
  Nat.card {Q : Subgroup (Equiv.Perm AffineThreeTwo) //
      IsRegularQuaternionSubgroup Q} = 14 ∧
    Nat.card
      ({Q : Subgroup (Equiv.Perm AffineThreeTwo) // IsRegularQuaternionSubgroup Q} ×
       {Q : Subgroup (Equiv.Perm AffineThreeTwo) // IsRegularQuaternionSubgroup Q}) = 196

def IsCentralInvolution
    (Q : Subgroup (Equiv.Perm AffineThreeTwo))
    (z : Equiv.Perm AffineThreeTwo) : Prop :=
  z ∈ Q ∧ z ≠ 1 ∧ z * z = 1 ∧ ∀ q : Q, z * q.1 = q.1 * z

def ConjugateInAGL
    (Q R : Subgroup (Equiv.Perm AffineThreeTwo)) : Prop :=
  ∃ g : AGLThreeTwo, ∀ x : Equiv.Perm AffineThreeTwo,
    x ∈ R ↔ g.1 * x * (g.1)⁻¹ ∈ Q

/-- Claim 38309: a nonconjugate order-32 local pair still has one center. -/
def claim38309 : Prop :=
  ∃ Q R : Subgroup (Equiv.Perm AffineThreeTwo),
    IsRegularQuaternionSubgroup Q ∧
    IsRegularQuaternionSubgroup R ∧
    Nat.card (↥(Q ⊔ R)) = 32 ∧
    ¬ ConjugateInAGL Q R ∧
    ∃ z : Equiv.Perm AffineThreeTwo,
      IsCentralInvolution Q z ∧ IsCentralInvolution R z

/-- The translation subgroup of the permutation group of an additive group. -/
def translationSubgroup (V : Type*) [AddGroup V] : Subgroup (Equiv.Perm V) :=
  Subgroup.closure (Set.range (fun v : V => Equiv.addRight v))

def IsPermutationBlock
    {V : Type*} [AddGroup V]
    (H : Subgroup (Equiv.Perm V)) (B : Set V) : Prop :=
  B.Nonempty ∧
    ∀ h : H,
      Set.image h.1 B = B ∨ Disjoint (Set.image h.1 B) B

def IsPrimitivePermutationGroup
    {V : Type*} [AddGroup V]
    (H : Subgroup (Equiv.Perm V)) : Prop :=
  ∀ B : Set V, IsPermutationBlock H B → Set.Subsingleton B ∨ B = Set.univ

def IsAffinePrimitivePermutationGroup
    {V : Type*} [AddGroup V] [Fintype V] [DecidableEq V]
    (H : Subgroup (Equiv.Perm V)) : Prop :=
  translationSubgroup V ≤ H ∧
    (∀ h : H, ∀ t : translationSubgroup V,
      h.1 * t.1 * (h.1)⁻¹ ∈ translationSubgroup V) ∧
    IsPrimitivePermutationGroup H

def IsNormalSubgroupOf
    {G : Type*} [Group G]
    (N H : Subgroup G) : Prop :=
  N ≤ H ∧ ∀ n ∈ N, ∀ h ∈ H, h * n * h⁻¹ ∈ N

def IsNontrivialSubgroup
    {G : Type*} [Group G] (N : Subgroup G) : Prop :=
  ∃ n, n ∈ N ∧ n ≠ 1

def IsNormalPSubgroup
    {G : Type*} [Group G]
    (p : ℕ) (N H : Subgroup G) : Prop :=
  IsNormalSubgroupOf N H ∧ IsPGroup p N

def IsLargestNormalPSubgroup
    {G : Type*} [Group G]
    (p : ℕ) (T H : Subgroup G) : Prop :=
  IsNormalPSubgroup p T H ∧
    ∀ N : Subgroup G, IsNormalPSubgroup p N H → N ≤ T

def IsDisjointFrom
    {G : Type*} [Group G]
    (N T : Subgroup G) : Prop :=
  ∀ x, x ∈ N → x ∈ T → x = 1

def centralizerSet
    {G : Type*} [Group G] (T : Subgroup G) : Set G :=
  {g | ∀ t : T, g * t.1 = t.1 * g}

/-- Claim 38319: the affine translation socle is forced into every
nontrivial normal subgroup, with the stated disjointness and centralizer
facts. -/
def claim38319 : Prop :=
  ∀ (p : ℕ) [Fact (Nat.Prime p)] (V : Type*)
    [AddCommGroup V] [Module (ZMod p) V] [Fintype V] [DecidableEq V]
    (H : Subgroup (Equiv.Perm V)),
    IsAffinePrimitivePermutationGroup H →
      (∀ N : Subgroup (Equiv.Perm V),
        IsNormalSubgroupOf N H →
        IsNontrivialSubgroup N →
        translationSubgroup V ≤ N) ∧
      (∀ N : Subgroup (Equiv.Perm V),
        IsNormalSubgroupOf N H →
        IsDisjointFrom N (translationSubgroup V) →
        ∀ n ∈ N, ∀ t : translationSubgroup V, n * t.1 = t.1 * n) ∧
      centralizerSet (translationSubgroup V) =
        (translationSubgroup V : Set (Equiv.Perm V))

def IsFaithfulIrreducibleAffineComplement
    (p : ℕ) {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (H H₀ : Subgroup (Equiv.Perm V)) : Prop :=
  H₀ ≤ H ∧
    (∀ h : H₀, h.1 0 = 0 ∧
      (∀ x y : V, h.1 (x + y) = h.1 x + h.1 y)) ∧
    (∀ h : H, ∃ t : translationSubgroup V, ∃ h₀ : H₀,
      h.1 = t.1 * h₀.1) ∧
    (∀ h : H₀, (∀ x : V, h.1 x = x) → h = 1) ∧
    (∀ W : AddSubgroup V,
      (∀ h : H₀, ∀ w ∈ W, h.1 w ∈ W) → W = ⊥ ∨ W = ⊤)

/-- Claim 38320: the translation socle is the largest normal `p`-subgroup. -/
def claim38320 : Prop :=
  ∀ (p : ℕ) [Fact (Nat.Prime p)] (V : Type*)
    [AddCommGroup V] [Module (ZMod p) V] [Fintype V] [DecidableEq V]
    (H H₀ : Subgroup (Equiv.Perm V)),
    IsAffinePrimitivePermutationGroup H →
    IsFaithfulIrreducibleAffineComplement p H H₀ →
    IsLargestNormalPSubgroup p (translationSubgroup V) H

/-- A crossed homomorphism to `ZMod n` for a character acting by units. -/
def IsCrossedHomomorphism
    {n : ℕ} {D : Type*} [Group D]
    (χ : D →* (ZMod n)ˣ) (f : D → ZMod n) : Prop :=
  ∀ g h : D, f (g * h) = f g + (χ g : ZMod n) * f h

def IsInversionCharacter
    {n : ℕ} {D : Type*} [Group D]
    (χ : D →* (ZMod n)ˣ) : Prop :=
  ∀ g : D, χ g = 1 ∨ χ g = -1

def IsCoboundaryForCharacter
    {n : ℕ} {D : Type*} [Group D]
    (χ : D →* (ZMod n)ˣ) (f : D → ZMod n) : Prop :=
  ∃ c : ZMod n, ∀ g : D, f g = c * (1 - (χ g : ZMod n))

/-- Claim 38356: every support-stabilizer cocycle is a coboundary over
`C₃₅`, and the same conclusion holds modulo 5 and modulo 7. -/
def claim38356 : Prop :=
  ∀ (D : Type*) [Group D] [Fintype D],
    (Fintype.card D = 1 ∨ Fintype.card D = 2 ∨
      Fintype.card D = 4 ∨ Fintype.card D = 8) →
    (∀ (χ : D →* (ZMod 35)ˣ),
      IsInversionCharacter χ →
      ∀ f : D → ZMod 35,
        IsCrossedHomomorphism χ f → IsCoboundaryForCharacter χ f) ∧
    (∀ (χ : D →* (ZMod 5)ˣ),
      IsInversionCharacter χ →
      ∀ f : D → ZMod 5,
        IsCrossedHomomorphism χ f → IsCoboundaryForCharacter χ f) ∧
    (∀ (χ : D →* (ZMod 7)ˣ),
      IsInversionCharacter χ →
      ∀ f : D → ZMod 7,
        IsCrossedHomomorphism χ f → IsCoboundaryForCharacter χ f)

abbrev BooleanSquare := ZMod 2 × ZMod 2
abbrev BooleanSwitchSpace := BooleanSquare × ZMod 2

def booleanSwitchA : BooleanSquare := (1, 0)

def booleanSwitchB (x : BooleanSquare) : ZMod 2 := x.1 * x.2

def booleanSwitch (p : BooleanSwitchSpace) : BooleanSwitchSpace :=
  (p.1, p.2 + booleanSwitchB p.1)

def cayleyAdjacency (S : Set BooleanSwitchSpace)
    (x y : BooleanSwitchSpace) : Prop :=
  y - x ∈ S

def IsCayleyAutomorphism (S : Set BooleanSwitchSpace)
    (f : BooleanSwitchSpace → BooleanSwitchSpace) : Prop :=
  Function.Bijective f ∧
    ∀ x y : BooleanSwitchSpace,
      (cayleyAdjacency S x y ↔ cayleyAdjacency S (f x) (f y))

/-- Claim 38325: the explicit Boolean-switching counterfeit. -/
def claim38325 : Prop :=
  let a : BooleanSquare := booleanSwitchA
  let b : BooleanSquare → ZMod 2 := booleanSwitchB
  let S : Set BooleanSwitchSpace := {(a, 0)}
  b a = 0 ∧
    (∀ x : BooleanSquare,
      b (x + a) + b x = x.2) ∧
    Fintype.card {x : BooleanSquare // b (x + a) + b x = 0} = 2 ∧
    Fintype.card {x : BooleanSquare // b (x + a) + b x = 1} = 2 ∧
    (∀ (x : BooleanSquare) (e d : ZMod 2),
      (booleanSwitch (x + a, e + d) - booleanSwitch (x, e)).2 =
        d + b (x + a) + b x) ∧
    ¬ IsCayleyAutomorphism S booleanSwitch

def IsPermutationBlock35
    (L : Subgroup (Equiv.Perm (Fin 35))) (B : Set (Fin 35)) : Prop :=
  B.Nonempty ∧
    ∀ g : L,
      Set.image g.1 B = B ∨ Disjoint (Set.image g.1 B) B

def IsPrimitivePermutationSubgroup35
    (L : Subgroup (Equiv.Perm (Fin 35))) : Prop :=
  (∀ x y : Fin 35, ∃ g : L, g.1 x = y) ∧
    (∀ B : Set (Fin 35), IsPermutationBlock35 L B →
      Set.Subsingleton B ∨ B = Set.univ)

def IsLiteralPartition35
    (P : Set (Set (Fin 35))) (cellCount cellSize : ℕ) : Prop :=
  P.Finite ∧ P.ncard = cellCount ∧
    Set.PairwiseDisjoint P id ∧ Set.sUnion P = Set.univ ∧
    ∀ C ∈ P, C.Finite ∧ C.ncard = cellSize

def PreservesLiteralPartition35
    (L : Subgroup (Equiv.Perm (Fin 35)))
    (P : Set (Set (Fin 35))) : Prop :=
  ∀ g : L, ∀ C ∈ P, ∃ C' ∈ P, Set.image g.1 C = C'

def Alternating35 : Subgroup (Equiv.Perm (Fin 35)) :=
  Subgroup.comap (Equiv.Perm.sign) (⊥ : Subgroup ℤˣ)

def IsImprimitivePrimePartition35
    (L : Subgroup (Equiv.Perm (Fin 35))) : Prop :=
  (∃ P : Set (Set (Fin 35)),
    IsLiteralPartition35 P 7 5 ∧ PreservesLiteralPartition35 L P) ∨
  (∃ P : Set (Set (Fin 35)),
    IsLiteralPartition35 P 5 7 ∧ PreservesLiteralPartition35 L P)

/-- Claim 38359: the one-fibre primitive/imprimitive dichotomy. -/
def claim38359 : Prop :=
  ∀ ρ f : Equiv.Perm (Fin 35),
    ρ.IsCycle ∧ ρ.support = Finset.univ →
    let L : Subgroup (Equiv.Perm (Fin 35)) :=
      Subgroup.closure {ρ, f⁻¹ * ρ * f}
    (IsPrimitivePermutationSubgroup35 L ∧
      (L = Alternating35 ∨ L = ⊤)) ∨
    (¬ IsPrimitivePermutationSubgroup35 L ∧
      IsImprimitivePrimePartition35 L)

end MathlibPlus.Open.ResearchFormalizationBatch01Worker01a000eb
