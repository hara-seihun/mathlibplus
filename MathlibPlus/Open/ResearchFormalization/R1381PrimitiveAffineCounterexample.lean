import MathlibPlus.Open.RepresentationTheory.AdmittedR1381
import MathlibPlus.Open.ResearchFormalization.MinimumBlockAction
import MathlibPlus.Open.Research.R1661

namespace MathlibPlus.Open.ResearchFormalization.R1381PrimitiveAffineCounterexample

noncomputable section

open MathlibPlus.Open.RepresentationTheory.R1381
open MathlibPlus.Open.Research.R1661
open MathlibPlus.Open.ResearchFormalization

abbrev Q8 := QuaternionGroup 2
abbrev Plane (p : ℕ) := Fin 2 → ZMod p
abbrev GL2 (p : ℕ) := Matrix.GeneralLinearGroup (Fin 2) (ZMod p)
abbrev ProductGroup (p : ℕ) := Multiplicative (Plane p) × Q8

/-- The action of the displayed quaternion representation on the plane. -/
def rhoAction {p : ℕ} [NeZero p] (ρ : Q8 →* GL2 p) (h : Q8) (v : Plane p) : Plane p :=
  Matrix.mulVec (ρ h : Matrix (Fin 2) (Fin 2) (ZMod p)) v

/-- The exact matrix, faithfulness, and irreducibility data for the Q8
representation used in the counterexample family. -/
def q8RepresentationData (p : ℕ) [NeZero p] (a b : ZMod p)
    (ρ : Q8 →* GL2 p) : Prop :=
  a ^ 2 + b ^ 2 = -1 ∧
    let i := q8MatrixI p
    let j := q8MatrixJ p a b
    let minus := q8MatrixMinusIdentity p
    i * i = minus ∧
      j * j = minus ∧
        i * j = -(j * i) ∧
          (ρ (QuaternionGroup.a 1) : Matrix (Fin 2) (Fin 2) (ZMod p)) = i ∧
            (ρ (QuaternionGroup.xa 0) : Matrix (Fin 2) (Fin 2) (ZMod p)) = j ∧
              MonoidHom.ker ρ = ⊥ ∧
                (ρ (QuaternionGroup.a 2) : Matrix (Fin 2) (Fin 2) (ZMod p)) = minus ∧
                  q8TwoDimensionalIrreducible ρ

/-- The representation chart on the underlying set of `C_p² × Q8`. -/
def chartFunction {p : ℕ} [NeZero p] (ρ : Q8 →* GL2 p) :
    ProductGroup p → ProductGroup p :=
  fun z =>
    (Multiplicative.ofAdd (rhoAction ρ z.2 (Multiplicative.toAdd z.1)), z.2)

def chartPermutation {p : ℕ} [NeZero p] (ρ : Q8 →* GL2 p)
    (f : Equiv.Perm (ProductGroup p)) : Prop :=
  ∀ z : ProductGroup p, f z = chartFunction ρ z

/-- The normalized directed relative derivative from the representation chart. -/
def normalizedDerivative {p : ℕ} [NeZero p] (ρ : Q8 →* GL2 p)
    (x : Plane p) (k : Q8) (z : ProductGroup p) : ProductGroup p :=
  let h := z.2
  let rk : Matrix (Fin 2) (Fin 2) (ZMod p) :=
    (ρ k : Matrix (Fin 2) (Fin 2) (ZMod p))
  let rhk : Matrix (Fin 2) (Fin 2) (ZMod p) :=
    (((ρ h)⁻¹ * ρ k : GL2 p) : Matrix (Fin 2) (Fin 2) (ZMod p))
  (Multiplicative.ofAdd
      (rhoAction ρ k (Multiplicative.toAdd z.1) +
        Matrix.mulVec (rk - rhk) x), h)

def derivativeStep {p : ℕ} [NeZero p] (ρ : Q8 →* GL2 p)
    (z w : ProductGroup p) : Prop :=
  ∃ x : Plane p, ∃ k : Q8,
    w = normalizedDerivative ρ x k z

/-- The directed normalized relative-derivative orbit carrier. -/
def derivativeOrbit {p : ℕ} [NeZero p] (ρ : Q8 →* GL2 p)
    (z : ProductGroup p) : Set (ProductGroup p) :=
  {w | Relation.ReflTransGen (derivativeStep ρ) z w}

/-- Orbital harmlessness records orbit fixation itself and its setwise form.
It does not assert preservation of an arbitrary Cayley connection set. -/
def chartOrbitallyHarmless {p : ℕ} [NeZero p] (ρ : Q8 →* GL2 p)
    (f : Equiv.Perm (ProductGroup p)) : Prop :=
  chartPermutation ρ f ∧
    (∀ z : ProductGroup p, f z ∈ derivativeOrbit ρ z) ∧
      (∀ z : ProductGroup p,
        Set.image f (derivativeOrbit ρ z) = derivativeOrbit ρ z)

/-- The standard regular direct-product copy and its chart conjugate. -/
def standardRegularCopy (p : ℕ) [NeZero p] :
    Subgroup (Equiv.Perm (ProductGroup p)) :=
  Subgroup.closure (Set.range (fun g : ProductGroup p => Equiv.mulLeft g))

def conjugationHom {G : Type*} [Group G] (g : G) : G →* G :=
  (MulAut.conj g : G ≃* G).toMonoidHom

def conjugateSubgroup {G : Type*} [Group G]
    (g : G) (H : Subgroup G) : Subgroup G :=
  H.map (conjugationHom g)

def twistedRegularCopy {p : ℕ} [NeZero p] (f : Equiv.Perm (ProductGroup p))
    (R : Subgroup (Equiv.Perm (ProductGroup p))) :
    Subgroup (Equiv.Perm (ProductGroup p)) :=
  conjugateSubgroup f R

/-- The elementary-abelian translation layer in the first factor. -/
def translationLayer (p : ℕ) [NeZero p] :
    Subgroup (Equiv.Perm (ProductGroup p)) :=
  Subgroup.closure
    (Set.range (fun v : Plane p =>
      Equiv.mulLeft (Multiplicative.ofAdd v, (1 : Q8))))

/-- The eight common point-fibres indexed by Q8. -/
def q8Fiber (p : ℕ) [NeZero p] (h : Q8) : Set (ProductGroup p) :=
  {z | z.2 = h}

def q8FiberSystem (p : ℕ) [NeZero p] : Set (Set (ProductGroup p)) :=
  Set.range (q8Fiber p)

def commonBlock {p : ℕ} [NeZero p]
    (R T : Subgroup (Equiv.Perm (ProductGroup p)))
    (B : Set (ProductGroup p)) : Prop :=
  permutationSetBlock (R : Set (Equiv.Perm (ProductGroup p))) B ∧
    permutationSetBlock (T : Set (Equiv.Perm (ProductGroup p))) B

def commonBlockSystem {p : ℕ} [NeZero p]
    (R T : Subgroup (Equiv.Perm (ProductGroup p)))
    (𝓑 : Set (Set (ProductGroup p))) : Prop :=
  permutationSetBlockSystem (R : Set (Equiv.Perm (ProductGroup p))) 𝓑 ∧
    permutationSetBlockSystem (T : Set (Equiv.Perm (ProductGroup p))) 𝓑

/-- The kernel set of the generated action on the displayed common block
system. -/
def localBlockKernelSet {p : ℕ} [NeZero p]
    (X : Subgroup (Equiv.Perm (ProductGroup p)))
    (𝓑 : Set (Set (ProductGroup p))) : Set (Equiv.Perm (ProductGroup p)) :=
  {g | g ∈ (X : Set (Equiv.Perm (ProductGroup p))) ∧
    ∀ B : Set (ProductGroup p), B ∈ 𝓑 → g '' B = B}

def normalIn {p : ℕ} [NeZero p]
    (N X : Subgroup (Equiv.Perm (ProductGroup p))) : Prop :=
  N ≤ X ∧
    ∀ x : X, ∀ n : N,
      x.1 * n.1 * x.1⁻¹ ∈ N

/-- The translation layer is subdirect on all eight Q8 fibres. -/
def subdirectTranslationLayer {p : ℕ} [NeZero p]
    (N : Subgroup (Equiv.Perm (ProductGroup p))) : Prop :=
  ∀ v : Plane p, ∃ n : N, ∀ z : Plane p, ∀ h : Q8,
    n.1 (Multiplicative.ofAdd z, h) =
      (Multiplicative.ofAdd (z + v), h)

def translationLayerInsideBlockKernel {p : ℕ} [NeZero p]
    (N : Subgroup (Equiv.Perm (ProductGroup p)))
    (X : Subgroup (Equiv.Perm (ProductGroup p)))
    (𝓑 : Set (Set (ProductGroup p))) : Prop :=
  ∀ n : N,
    n.1 ∈ localBlockKernelSet X 𝓑

/-- Every local block-kernel action contains the affine maps with linear part
from the displayed irreducible Q8 representation and arbitrary translation. -/
def primitiveAffineLocalKernel {p : ℕ} [NeZero p]
    (ρ : Q8 →* GL2 p)
    (X : Subgroup (Equiv.Perm (ProductGroup p)))
    (𝓑 : Set (Set (ProductGroup p))) (h : Q8) : Prop :=
  primitivePermutationSet
      (inducedLocalPermutations
        (localBlockKernelSet X 𝓑) (q8Fiber p h)) ∧
    (∀ v : Plane p, ∀ q : Q8,
      ∃ g : Equiv.Perm (ProductGroup p),
        g ∈ localBlockKernelSet X 𝓑 ∧
          ∀ z : Plane p,
            g (Multiplicative.ofAdd z, h) =
              (Multiplicative.ofAdd (v + rhoAction ρ q z), h))

def minimumCommonBlockSize (p : ℕ) [NeZero p]
    (R T : Subgroup (Equiv.Perm (ProductGroup p))) : Prop :=
  ∀ B : Set (ProductGroup p), commonBlock R T B →
    B ≠ Set.univ → ¬ Set.Subsingleton B →
      p ^ 2 ≤ Set.ncard B

def displayedMinimumCommonFibers (p : ℕ) [NeZero p]
    (R T : Subgroup (Equiv.Perm (ProductGroup p))) : Prop :=
  commonBlockSystem R T (q8FiberSystem p) ∧
    (∀ h : Q8,
      commonBlock R T (q8Fiber p h) ∧
        Set.ncard (q8Fiber p h) = p ^ 2) ∧
      minimumCommonBlockSize p R T

/-- A prime-point line partition in one Q8 fibre, induced by an additive
order-`p` line in the plane. -/
def lineBlock (p : ℕ) [NeZero p] (W : AddSubgroup (Plane p))
    (v : Plane p) (h : Q8) : Set (ProductGroup p) :=
  Set.image
    (fun w : Plane p => (Multiplicative.ofAdd (v + w), h))
    (W : Set (Plane p))

def linePartition (p : ℕ) [NeZero p] (W : AddSubgroup (Plane p)) :
    Set (Set (ProductGroup p)) :=
  {B | ∃ v : Plane p, ∃ h : Q8, B = lineBlock p W v h}

def twistedLinePartition (p : ℕ) [NeZero p] (f : Equiv.Perm (ProductGroup p))
    (W : AddSubgroup (Plane p)) : Set (Set (ProductGroup p)) :=
  {B | ∃ C : Set (ProductGroup p),
    C ∈ linePartition p W ∧ B = f '' C}

/-- Source and target order-`p` lines do not induce one common global
p-point refinement. -/
def commonPrimeLineRefinement (p : ℕ) [NeZero p]
    (f : Equiv.Perm (ProductGroup p)) : Prop :=
  ∃ W U : AddSubgroup (Plane p),
    Nat.card W = p ∧
      Nat.card U = p ∧
        linePartition p W = twistedLinePartition p f U

/-- Claim 38426: for every odd prime, the exact `C_p² × Q8` representation
chart yields two regular copies with genuine minimum `p²` common fibres, a
normal subdirect elementary-abelian translation layer inside primitive affine
local block kernels, no common prime-line refinement, and orbital (rather than
arbitrary-connection-set) harmlessness. -/
def claim38426 : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p), Odd p →
    letI : NeZero p := ⟨hp.ne_zero⟩
    ∃ a b : ZMod p, ∃ ρ : Q8 →* GL2 p,
      q8RepresentationData p a b ρ ∧
        let R := standardRegularCopy p
        ∃ f : Equiv.Perm (ProductGroup p),
          chartPermutation ρ f ∧
            let T := twistedRegularCopy f R
            let X := R ⊔ T
            let 𝓑 := q8FiberSystem p
            let N := translationLayer p
            MathlibPlus.Open.Research.R1661.isRegular R ∧
              MathlibPlus.Open.Research.R1661.isRegular T ∧
                commonBlockSystem R T 𝓑 ∧
                  normalIn N X ∧
                    MathlibPlus.Open.Research.R1661.isElementaryAbelian p N ∧
                      subdirectTranslationLayer N ∧
                        translationLayerInsideBlockKernel N X 𝓑 ∧
                          (∀ h : Q8, primitiveAffineLocalKernel ρ X 𝓑 h) ∧
                            displayedMinimumCommonFibers p R T ∧
                              ¬ commonPrimeLineRefinement p f ∧
                                chartOrbitallyHarmless ρ f

end

end MathlibPlus.Open.ResearchFormalization.R1381PrimitiveAffineCounterexample
