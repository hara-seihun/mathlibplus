import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Parity

noncomputable section

open Filter Set MeasureTheory
open scoped BigOperators Topology

/-- The `L²` space on the positive interval with the restricted Lebesgue measure. -/
abbrev L2On (a : ℝ) : Type :=
  MeasureTheory.Lp ℂ 2 ((volume : Measure ℝ).restrict (Ioc 0 a))

abbrev L2SymmetricOn (a : ℝ) : Type :=
  MeasureTheory.Lp ℂ 2 ((volume : Measure ℝ).restrict (Ioo (-a) a))

def coeL2On (a : ℝ) (f : L2On a) : ℝ → ℂ :=
  ↑↑(show MeasureTheory.Lp ℂ 2 ((volume : Measure ℝ).restrict (Ioc 0 a)) from f)

def coeL2SymmetricOn (a : ℝ) (g : L2SymmetricOn a) : ℝ → ℂ :=
  ↑↑(show MeasureTheory.Lp ℂ 2 ((volume : Measure ℝ).restrict (Ioo (-a) a)) from g)

/-- Even and odd `L²(-a,a)` subspaces, represented by almost-everywhere
parity. -/
abbrev EvenL2 (a : ℝ) :=
  {g : L2SymmetricOn a //
    ∀ᵐ x : ℝ ∂(volume.restrict (Ioo (-a) a)),
      coeL2SymmetricOn a g (-x) = coeL2SymmetricOn a g x}

abbrev OddL2 (a : ℝ) :=
  {g : L2SymmetricOn a //
    ∀ᵐ x : ℝ ∂(volume.restrict (Ioo (-a) a)),
      coeL2SymmetricOn a g (-x) = -coeL2SymmetricOn a g x}

/-- The exact formula, bijectivity, and isometry required of the two natural
parity folds. -/
def NaturalParityFoldMaps (a : ℝ) : Prop :=
  ∃ Ue : L2On a → EvenL2 a, ∃ Uo : L2On a → OddL2 a,
    Isometry Ue ∧ Isometry Uo ∧ Function.Bijective Ue ∧ Function.Bijective Uo ∧
      (∀ f : L2On a,
        ∀ᵐ x : ℝ ∂(volume.restrict (Ioo (-a) a)),
          coeL2SymmetricOn a (Ue f).1 x =
              (Real.sqrt 2)⁻¹ * coeL2On a f |x| ∧
            coeL2SymmetricOn a (Uo f).1 x =
              (Real.sqrt 2)⁻¹ * Complex.ofReal (Real.sign x) *
                coeL2On a f |x|)

/-- Natural parity-fold maps from `L²(0,a)` to the even and odd sectors. -/
def claim_12401 : Prop :=
  ∀ a : ℝ, 0 < a → NaturalParityFoldMaps a

/-- The archimedean geometric kernel appearing in the reflected formulas. -/
def archimedeanJ (t : ℝ) : ℝ :=
  Real.exp (-|t| / 2) / (1 - Real.exp (-2 * |t|))

def archimedeanHankelKernel (x y : ℝ) : ℝ := archimedeanJ (x + y)

def exponentialPhi (m : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-(((2 * m : ℝ) + (1 / 2 : ℝ)) * x))

/-- The geometric expansion of the reflected archimedean kernel. -/
def claim_12404 : Prop :=
  ∀ x y : ℝ, 0 < x → 0 < y →
    archimedeanJ (x + y) =
      ∑' m : ℕ, exponentialPhi m x * exponentialPhi m y

/-- The real `L²` pairing on an interval. -/
def intervalInner (δ : ℝ) (f g : ℝ → ℝ) : ℝ :=
  ∫ x in Ioc 0 δ, f x * g x

def hankelForm (δ : ℝ) (f g : ℝ → ℝ) : ℝ :=
  ∫ x in Ioc 0 δ, ∫ y in Ioc 0 δ,
    archimedeanJ (x + y) * f y * g x

def hankelOperator (δ : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y in Ioc 0 δ, archimedeanJ (x + y) * f y

def InfiniteRankOnInterval (δ : ℝ) : Prop :=
  ∀ r : ℕ, ∃ v : Fin r → (ℝ → ℝ),
    (∀ i, MemLp (v i) 2 (volume.restrict (Ioc 0 δ))) ∧
      LinearIndependent ℝ (fun i => hankelOperator δ (v i))

/-- The Hankel form identity, positive definiteness on every initial span, and
unbounded rank asserted for `J(x+y)`. -/
def claim_12406 : Prop :=
  ∀ δ : ℝ, 0 < δ →
    (∀ f : ℝ → ℝ,
      MemLp f 2 (volume.restrict (Ioc 0 δ)) →
        hankelForm δ f f =
          ∑' m : ℕ, |intervalInner δ f (exponentialPhi m)| ^ 2) ∧
      (∀ r : ℕ,
        Matrix.PosDef
          (fun i j : Fin r =>
            intervalInner δ (exponentialPhi i) (exponentialPhi j))) ∧
      InfiniteRankOnInterval δ

end

end MathlibPlus.Open.ResearchFormalization.Parity
