import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch_01a000fb67dc71b3a12d9eaf958b53bc

noncomputable section

/-! The finite Cayley model used for the mod-two support relation. -/

abbrev BinaryNine (r : ℕ) := (Fin r → ZMod 2) × ZMod 9

def inverseClosed {G : Type} [AddGroup G] (S : Finset G) : Prop :=
  ∀ s, s ∈ S ↔ -s ∈ S

def cayleyAdjacency {r : ℕ} (S : Finset (BinaryNine r))
    (x y : BinaryNine r) : ZMod 2 :=
  if x - y ∈ S then 1 else 0

def cayleyAdjacencySquare {r : ℕ} (S : Finset (BinaryNine r))
    (x y : BinaryNine r) : ZMod 2 :=
  ∑ z : BinaryNine r, cayleyAdjacency S x z * cayleyAdjacency S z y

def squareSupportStep {r : ℕ} (S : Finset (BinaryNine r))
    (x y : BinaryNine r) : Prop :=
  cayleyAdjacencySquare S x y ≠ 0

def squareSupportConnected {r : ℕ} (S : Finset (BinaryNine r))
    (x y : BinaryNine r) : Prop :=
  Relation.ReflTransGen
    (fun a b => squareSupportStep S a b ∨ squareSupportStep S b a) x y

def doubled {r : ℕ} (s : BinaryNine r) : BinaryNine r := s + s

def oddPowerCoefficient {r : ℕ} (S : Finset (BinaryNine r))
    (g : BinaryNine r) : Prop :=
  (S.filter (fun s => doubled s = g)).card % 2 = 1

def kTwoGenerators {r : ℕ} (S : Finset (BinaryNine r)) : Set (BinaryNine r) :=
  {g | oddPowerCoefficient S g}

def kTwo {r : ℕ} (S : Finset (BinaryNine r)) : AddSubgroup (BinaryNine r) :=
  AddSubgroup.closure (kTwoGenerators S)

def nineAxis (r : ℕ) : AddSubgroup (BinaryNine r) :=
  (⊥ : AddSubgroup (Fin r → ZMod 2)).prod (⊤ : AddSubgroup (ZMod 9))

def kTwoCoset {r : ℕ} (K : AddSubgroup (BinaryNine r))
    (x : BinaryNine r) : Set (BinaryNine r) :=
  {y | y - x ∈ K}

/-- Claim 54033: the connected components of the mod-two support of the
adjacency square are the cosets of the odd doubled-support subgroup. -/
def claim54033 : Prop :=
  ∀ (r : ℕ) (S : Finset (BinaryNine r)),
    inverseClosed S →
      let K := kTwo S
      K ≤ nineAxis r ∧
        ∀ x y, squareSupportConnected S x y ↔ y ∈ kTwoCoset K x

/-! The characteristic-three group algebra of the cyclic group of order nine. -/

abbrev C9GroupAlgebra := AddMonoidAlgebra (ZMod 3) (ZMod 9)

def c9Basis (a : ZMod 9) : C9GroupAlgebra :=
  AddMonoidAlgebra.single a 1

def z9 : C9GroupAlgebra := c9Basis 1

def z9Inverse : C9GroupAlgebra := c9Basis (-1)

def u9 : C9GroupAlgebra := z9 - 1

def w9 : C9GroupAlgebra := z9 + z9Inverse - 2

def inversionOnC9Algebra (x : C9GroupAlgebra) : C9GroupAlgebra :=
  x.coeff.sum (fun a c => AddMonoidAlgebra.single (-a) c)

def inversionFixedSpan : Submodule (ZMod 3) C9GroupAlgebra :=
  Submodule.span (ZMod 3) {x | inversionOnC9Algebra x = x}

def hasUValuationTwo (x : C9GroupAlgebra) : Prop :=
  (∃ y, x = u9 ^ 2 * y) ∧ ¬ ∃ y, x = u9 ^ 3 * y

def c9QuotientIdeal : Ideal (Polynomial (ZMod 3)) :=
  Ideal.span ({Polynomial.X ^ 5} : Set (Polynomial (ZMod 3)))

/-- Claim 54056: the inversion-fixed part is the length-five local algebra
on the nilpotent generator `w`, with the stated Frobenius identities. -/
def claim54056 : Prop :=
  (∃ φ : (Polynomial (ZMod 3) ⧸ c9QuotientIdeal) →ₐ[ZMod 3] C9GroupAlgebra,
      Function.Injective φ ∧
      (∀ x, inversionOnC9Algebra x = x ↔ x ∈ φ.range) ∧
      Module.finrank (ZMod 3) φ.range = 5 ∧
      φ (Ideal.Quotient.mk c9QuotientIdeal Polynomial.X) = w9) ∧
    Module.finrank (ZMod 3) inversionFixedSpan = 5 ∧
    hasUValuationTwo w9 ∧
    w9 ^ 3 = u9 ^ 6 ∧
    u9 ^ 6 = 1 + z9 ^ 3 + z9 ^ 6 ∧
    w9 ^ 5 = 0 ∧
    LinearIndependent (ZMod 3) (fun i : Fin 5 => w9 ^ (i : ℕ))

/-! The explicitly displayed degree-729 marked-shear span. -/

abbrev MarkedH := Fin 5 → ZMod 3
abbrev MarkedFunction := MarkedH → ZMod 3

def markedKGenerator : Fin 6 → MarkedFunction
  | 0 => fun _ => 1
  | 1 => fun h => h 0
  | 2 => fun h => h 2
  | 3 => fun h => h 0 ^ 2
  | 4 => fun h => h 0 * h 2
  | 5 => fun h => h 2 ^ 2

def markedK : Submodule (ZMod 3) MarkedFunction :=
  Submodule.span (ZMod 3) (Set.range markedKGenerator)

def markedQuotientPermutation (h : MarkedH) : MarkedH :=
  ![h 0,
    h 1,
    h 2 + h 0 * (h 0 - 1),
    h 3 + (2 * h 0 - 1) * h 1,
    h 4 + h 1 ^ 2]

def markedShearImage : Submodule (ZMod 3) MarkedFunction :=
  Submodule.span (ZMod 3)
    {f | ∃ k ∈ markedK, f = k ∘ markedQuotientPermutation}

def markedShearSpan : Submodule (ZMod 3) MarkedFunction :=
  markedK ⊔ markedShearImage

noncomputable instance markedShearSpanFintype : Fintype markedShearSpan :=
  Fintype.ofFinite _

noncomputable instance markedKFintype : Fintype markedK :=
  Fintype.ofFinite _

noncomputable instance markedOutsideKFintype :
    Fintype {f : MarkedFunction // f ∈ markedShearSpan ∧ f ∉ markedK} :=
  Fintype.ofFinite _

/-- Claim 54064: the displayed marked-shear span has the exact dimension and
finite split stated in the packet. -/
def claim54064 : Prop :=
  Module.finrank (ZMod 3) markedShearSpan = 7 ∧
    Fintype.card markedShearSpan = 3 ^ 7 ∧
    Fintype.card markedK = 3 ^ 6 ∧
    Fintype.card {f : MarkedFunction // f ∈ markedShearSpan ∧ f ∉ markedK} = 2 * 3 ^ 6

end
end MathlibPlus.Open.ResearchFormalizationBatch_01a000fb67dc71b3a12d9eaf958b53bc
