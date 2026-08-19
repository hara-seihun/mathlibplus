import MathlibPlus.Open.ResearchFormalization.R1330Claim41027

namespace MathlibPlus.Open.ResearchFormalization.R1330Claim41029

noncomputable section

open MathlibPlus.Open.Research.R1330Formalization_41037
open MathlibPlus.Open.ResearchFormalization.R1330Claim41027

/-- The vertical and horizontal fibres on which the two shears act. -/
def binomialFiber (p : ℕ) (x : ZMod p) : Set (V p) :=
  {z | z.1 = x}

def binomialFiberSecond (p : ℕ) (y : ZMod p) : Set (V p) :=
  {z | z.2 = y}

def binomialTrivialFiber (p : ℕ) (x : ZMod p) : Prop :=
  binomTwo p x = 0

def nontrivialBinomialFiberCount (p : ℕ) : Prop :=
  Nat.card {x : ZMod p // ¬ binomialTrivialFiber p x} = p - 2

/-- Exact `p`-cycle action on a nontrivial vertical fibre. -/
def firstFiberIsPCycle (p : ℕ) (A : Equiv.Perm (V p))
    (x : ZMod p) : Prop :=
  (∀ z : V p, z ∈ binomialFiber p x →
    A z = (x, z.2 + binomTwo p x)) ∧
    (∀ y : ZMod p,
      (A ^ p) (x, y) = (x, y) ∧
        (∀ n : ℕ, 0 < n → n < p →
          (A ^ n) (x, y) ≠ (x, y)))

/-- Exact `p`-cycle action on a nontrivial horizontal fibre. -/
def secondFiberIsPCycle (p : ℕ) (B : Equiv.Perm (V p))
    (y : ZMod p) : Prop :=
  (∀ z : V p, z ∈ binomialFiberSecond p y →
    B z = (z.1 + binomTwo p y, y)) ∧
    (∀ x : ZMod p,
      (B ^ p) (x, y) = (x, y) ∧
        (∀ n : ℕ, 0 < n → n < p →
          (B ^ n) (x, y) ≠ (x, y)))

/-- The complete product decomposition of the first shear into the
`p`-cycles on its nontrivial fibres, with its trivial fibres fixed. -/
def shearAFiberPCycles (p : ℕ) (A : Equiv.Perm (V p)) : Prop :=
  nontrivialBinomialFiberCount p ∧
    (∀ x : ZMod p, ¬ binomialTrivialFiber p x →
      firstFiberIsPCycle p A x) ∧
      (∀ x : ZMod p, binomialTrivialFiber p x →
        ∀ y : ZMod p, A (x, y) = (x, y))

/-- The complete product decomposition of the second shear into the
`p`-cycles on its nontrivial fibres, with its trivial fibres fixed. -/
def shearBFiberPCycles (p : ℕ) (B : Equiv.Perm (V p)) : Prop :=
  nontrivialBinomialFiberCount p ∧
    (∀ y : ZMod p, ¬ binomialTrivialFiber p y →
      secondFiberIsPCycle p B y) ∧
      (∀ y : ZMod p, binomialTrivialFiber p y →
        ∀ x : ZMod p, B (x, y) = (x, y))

/-- The two actual coordinate projections of the block kernel are contained
in the alternating group on the exact `p²`-point block. -/
def coordinateProjectionsAreAlternating
    (p : ℕ) [NeZero p] (F : Equiv.Perm (Ω p)) : Prop :=
  (∀ a : Equiv.Perm (V p),
    a ∈ rotationCoordinateProjection p F →
      a ∈ alternatingGroup (V p)) ∧
    (∀ b : Equiv.Perm (V p),
      b ∈ reflectionCoordinateProjection p F →
        b ∈ alternatingGroup (V p))

/-- Claim 41029: the pinned shears are even, their exact fibre cycle
 decompositions have `p-2` nontrivial `p`-cycles, and the actual rotation and
 reflection projections of the six-block kernel lie in `Alt(p²)`. -/
def claim41029 : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p), Odd p →
    letI : NeZero p := ⟨hp.ne_zero⟩
    ∃ F : Equiv.Perm (Ω p), ∃ A B : Equiv.Perm (V p),
      (∀ z : Ω p, F z = blockShear p z) ∧
        realizes A (shearA p) ∧
          realizes B (shearB p) ∧
            A ∈ alternatingGroup (V p) ∧
              B ∈ alternatingGroup (V p) ∧
                actsAsPair p A B F ∧
                  blockKernel p F F ∧
                    A ∈ rotationCoordinateProjection p F ∧
                      B ∈ reflectionCoordinateProjection p F ∧
                        shearAFiberPCycles p A ∧
                          shearBFiberPCycles p B ∧
                            coordinateProjectionsAreAlternating p F

end

end MathlibPlus.Open.ResearchFormalization.R1330Claim41029
