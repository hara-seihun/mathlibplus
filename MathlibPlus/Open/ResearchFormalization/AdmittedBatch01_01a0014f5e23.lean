import Mathlib

noncomputable section

open MeasureTheory
open Topology
open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization


open scoped BigOperators


/-- The folded kernel appearing in the exact tangency claim. -/
def foldedKernel (q s : ℝ) : ℝ :=
  Real.rpow s (-(5 : ℝ) / 4) * Real.exp (-q / s) +
    Real.rpow s ((5 : ℝ) / 4) * Real.exp (-q * s)

def crossThree (v w : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![v 1 * w 2 - v 2 * w 1,
    v 2 * w 0 - v 0 * w 2,
    v 0 * w 1 - v 1 * w 0]

/-- Claim 57868: the prescribed folded kernel has an exact double zero. -/
def foldedKernelExactTangency : Prop :=
  let q₀ : ℝ := 9 * Real.pi / 4
  let rates : Fin 3 → ℝ := ![2, 3, 5]
  let v : Fin 3 → ℝ := fun j => foldedKernel q₀ (rates j)
  let w : Fin 3 → ℝ :=
    fun j => deriv (fun q : ℝ => foldedKernel q (rates j)) q₀
  let c : Fin 3 → ℝ := crossThree v w
  let F : ℝ → ℝ := fun q => ∑ j : Fin 3, c j * foldedKernel q (rates j)
  let x₀ : ℝ := 3 / 2
  rates 0 = 2 ∧ rates 1 = 3 ∧ rates 2 = 5 ∧
    rates 0 < rates 1 ∧ rates 1 < rates 2 ∧
    F q₀ = 0 ∧ deriv F q₀ = 0 ∧ q₀ = Real.pi * x₀ ^ 2 ∧
      1 < x₀ ∧ x₀ < 2



open MeasureTheory


def dOnePointwise (x₀ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 2 * x₀; 0, 2]

def betaOnePointwise (x₀ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 2 * x₀; 1, 2 * x₀ - 2]

def uniformMeanOnHalfInterval (f : ℝ → ℝ) : ℝ :=
  (∫ x in (1 / 2 : ℝ)..(3 / 2 : ℝ), f x) /
    ((3 / 2 : ℝ) - (1 / 2 : ℝ))

/-- Claim 57878: the pointwise cup entry changes sign although its uniform mean vanishes. -/
def dOnePointwiseCupSignChange : Prop :=
  (∀ x₀ : ℝ,
      x₀ ∈ Set.Icc (1 / 2 : ℝ) (3 / 2 : ℝ) →
        (x₀ ∈ Set.Ico (1 / 2 : ℝ) 1 → betaOnePointwise x₀ 1 1 < 0) ∧
        (x₀ ∈ Set.Ioc 1 (3 / 2 : ℝ) → betaOnePointwise x₀ 1 1 > 0) ∧
        (betaOnePointwise x₀ 1 1 = 0 ↔ x₀ = 1)) ∧
    betaOnePointwise (1 / 2 : ℝ) = !![1, 1; 1, -1] ∧
    betaOnePointwise (1 / 2 : ℝ) 1 1 = -1 ∧
    uniformMeanOnHalfInterval (fun x : ℝ => 2 * x - 2) = 0 ∧
    uniformMeanOnHalfInterval (fun x : ℝ => x) = 1





/-- Projection onto the first factor of a two-summand direct sum. -/
def firstProjection (k E B : Type*) [Semiring k] [AddCommMonoid E] [AddCommMonoid B]
    [Module k E] [Module k B] : E × B →ₗ[k] E :=
  { toFun := fun x => x.1
    map_add' := by intro x y; rfl
    map_smul' := by intro a x; rfl }

def basisFamily (k ι E : Type*) [Field k] [AddCommGroup E] [Module k E]
    (e : ι → E) : Prop :=
  LinearIndependent k e ∧ Submodule.span k (Set.range e) = ⊤

/-- The support-separated cochain-complex hypotheses from claim 57881. -/
def supportSeparatedCochainHypotheses
    (k C1 C3 E B ι : Type*)
    [Field k] [AddCommGroup C1] [AddCommGroup C3]
    [AddCommGroup E] [AddCommGroup B]
    [Module k C1] [Module k C3] [Module k E] [Module k B]
    (d1 : C1 →ₗ[k] E × B) (d2 : E × B →ₗ[k] C3)
    (e : ι → E) : Prop :=
  basisFamily k ι E e ∧
    (∀ x, d2 (d1 x) = 0) ∧
    (∀ i, d2 (e i, 0) = 0) ∧
    (∀ x, firstProjection k E B (d1 x) = 0)

def dOneIntoKernel
    (k C1 C3 E B : Type*)
    [Field k] [AddCommGroup C1] [AddCommGroup C3]
    [AddCommGroup E] [AddCommGroup B]
    [Module k C1] [Module k C3] [Module k E] [Module k B]
    (d1 : C1 →ₗ[k] E × B) (d2 : E × B →ₗ[k] C3)
    (hcomplex : ∀ x, d2 (d1 x) = 0) :
    C1 →ₗ[k] LinearMap.ker d2 :=
  { toFun := fun x => ⟨d1 x, hcomplex x⟩
    map_add' := by
      intro x y
      apply Subtype.ext
      exact d1.map_add x y
    map_smul' := by
      intro a x
      apply Subtype.ext
      exact d1.map_smul a x }

def boundarySubmodule
    (k C1 C3 E B : Type*)
    [Field k] [AddCommGroup C1] [AddCommGroup C3]
    [AddCommGroup E] [AddCommGroup B]
    [Module k C1] [Module k C3] [Module k E] [Module k B]
    (d1 : C1 →ₗ[k] E × B) (d2 : E × B →ₗ[k] C3)
    (hcomplex : ∀ x, d2 (d1 x) = 0) :
    Submodule k (LinearMap.ker d2) :=
  LinearMap.range (dOneIntoKernel k C1 C3 E B d1 d2 hcomplex)

def secondCohomology
    (k C1 C3 E B : Type*)
    [Field k] [AddCommGroup C1] [AddCommGroup C3]
    [AddCommGroup E] [AddCommGroup B]
    [Module k C1] [Module k C3] [Module k E] [Module k B]
    (d1 : C1 →ₗ[k] E × B) (d2 : E × B →ₗ[k] C3)
    (hcomplex : ∀ x, d2 (d1 x) = 0) : Type _ :=
  (LinearMap.ker d2) ⧸ boundarySubmodule k C1 C3 E B d1 d2 hcomplex

def projectionOnKernel
    (k C3 E B : Type*)
    [Field k] [AddCommGroup C3] [AddCommGroup E] [AddCommGroup B]
    [Module k C3] [Module k E] [Module k B]
    (d2 : E × B →ₗ[k] C3) : LinearMap.ker d2 →ₗ[k] E :=
  (firstProjection k E B).comp (Submodule.subtype (LinearMap.ker d2))

/-- Claim 57882: the projected quotient map and the basis section exist exactly as stated. -/
def quotientDescendsSecondCohomology
    (k C1 C3 E B ι : Type*)
    [Field k] [AddCommGroup C1] [AddCommGroup C3]
    [AddCommGroup E] [AddCommGroup B]
    [Module k C1] [Module k C3] [Module k E] [Module k B]
    (d1 : C1 →ₗ[k] E × B) (d2 : E × B →ₗ[k] C3)
    (e : ι → E) : Prop :=
  basisFamily k ι E e →
  ∀ (hcomplex : ∀ x, d2 (d1 x) = 0)
    (he : ∀ i, d2 (e i, 0) = 0)
    (hboundary : ∀ x, firstProjection k E B (d1 x) = 0),
    let bd := boundarySubmodule k C1 C3 E B d1 d2 hcomplex
    let h2 := (LinearMap.ker d2) ⧸ bd
    let qker := projectionOnKernel k C3 E B d2
    ∃ qbar : h2 →ₗ[k] E, ∃ sec : E →ₗ[k] h2,
      (∀ x : LinearMap.ker d2,
        qbar ((Submodule.mkQ bd) x) = qker x) ∧
      Function.Surjective qbar ∧
      qbar.comp sec = (LinearMap.id : E →ₗ[k] E) ∧
      (∀ i, sec (e i) =
        (Submodule.mkQ bd) ⟨(e i, 0), he i⟩)

universe u

/-- Claim 57883: the section classes are independent and give the dimension bound. -/
def cohomologyDimensionLowerBound : Prop :=
  ∀ (k C1 C3 E B ι : Type u)
    [Field k] [AddCommGroup C1] [AddCommGroup C3]
    [AddCommGroup E] [AddCommGroup B]
    [Module k C1] [Module k C3] [Module k E] [Module k B]
    (d1 : C1 →ₗ[k] E × B) (d2 : E × B →ₗ[k] C3)
    (e : ι → E),
    quotientDescendsSecondCohomology k C1 C3 E B ι d1 d2 e →
    basisFamily k ι E e →
    ∀ (hcomplex : ∀ x, d2 (d1 x) = 0)
      (he : ∀ i, d2 (e i, 0) = 0)
      (hboundary : ∀ x, firstProjection k E B (d1 x) = 0),
      let bd := boundarySubmodule k C1 C3 E B d1 d2 hcomplex
      let h2 := (LinearMap.ker d2) ⧸ bd
      LinearIndependent k (fun i => (Submodule.mkQ bd) ⟨(e i, 0), he i⟩) ∧
        Cardinal.mk ι ≤ Module.rank k h2





abbrev HénonFp (p : ℕ) := ZMod p
abbrev HénonB (p m : ℕ) := Fin m → HénonFp p
abbrev HénonZ (p m : ℕ) := Fin m → HénonFp p
abbrev HénonW (p k : ℕ) := Fin k → HénonFp p
abbrev HénonV (p m k : ℕ) := HénonB p m × (HénonZ p m × HénonW p k)

def coordinateFunction (p m : ℕ) (f : Fin m → HénonFp p → HénonFp p)
    (z : HénonZ p m) : HénonB p m :=
  fun i => f i (z i)

def henonTheta (p m k : ℕ) (f : Fin m → HénonFp p → HénonFp p)
    (x : HénonB p m) (z : HénonZ p m) (w : HénonW p k) : HénonV p m k :=
  (z, (x + coordinateFunction p m f z, w))

def henonThetaInverse (p m k : ℕ) (f : Fin m → HénonFp p → HénonFp p)
    (x : HénonB p m) (z : HénonZ p m) (w : HénonW p k) : HénonV p m k :=
  (z - coordinateFunction p m f x, (x, w))

def henonPermutationClaim : Prop :=
  ∀ (p m k : ℕ), Nat.Prime p ∧ Odd p ∧ 1 ≤ m →
    ∀ (f : Fin m → HénonFp p → HénonFp p),
      (∀ i, f i 0 = 0) →
        let F := coordinateFunction p m f
        let thetaFn : HénonV p m k → HénonV p m k :=
          fun v => henonTheta p m k f v.1 v.2.1 v.2.2
        let thetaInvFn : HénonV p m k → HénonV p m k :=
          fun v => henonThetaInverse p m k f v.1 v.2.1 v.2.2
        Function.LeftInverse thetaInvFn thetaFn ∧
          Function.RightInverse thetaInvFn thetaFn ∧
          Function.Bijective thetaFn ∧
          thetaFn (0 : HénonV p m k) = 0

def periodSet (p : ℕ) (fᵢ : HénonFp p → HénonFp p) : Set (HénonFp p) :=
  {a | ∀ t u, fᵢ (t + a) - fᵢ t = fᵢ (u + a) - fᵢ u}

def isAdditiveSubgroupCarrier {A : Type*} [AddGroup A] (P : Set A) : Prop :=
  0 ∈ P ∧
    (∀ ⦃a b⦄, a ∈ P → b ∈ P → a + b ∈ P) ∧
    (∀ ⦃a⦄, a ∈ P → -a ∈ P)

def henonLinearPart (p m : ℕ) (f : Fin m → HénonFp p → HénonFp p)
    (z : HénonZ p m) : HénonB p m :=
  fun i =>
    if periodSet p (f i) = Set.univ then f i 1 * z i else 0

def scalarPeriodDichotomyClaim : Prop :=
  ∀ (p m : ℕ), Nat.Prime p ∧ Odd p ∧ 1 ≤ m →
    ∀ (f : Fin m → HénonFp p → HénonFp p),
      (∀ i, f i 0 = 0) →
        (∀ i,
          isAdditiveSubgroupCarrier (periodSet p (f i)) ∧
          (periodSet p (f i) = ({0} : Set (HénonFp p)) ∨
            periodSet p (f i) = Set.univ) ∧
          (periodSet p (f i) = Set.univ →
            ∀ t, f i t = t * f i 1))

/-- The scalar residual after removing the dichotomic linear part. -/
def henonResidual (p m : ℕ) (f : Fin m → HénonFp p → HénonFp p)
    (i : Fin m) (s : HénonFp p) : HénonFp p :=
  f i s - (if periodSet p (f i) = Set.univ then f i 1 * s else 0)

def henonDefect (p m : ℕ) (f : Fin m → HénonFp p → HénonFp p)
    (i : Fin m) (s a : HénonFp p) : HénonFp p :=
  henonResidual p m f i s +
    henonResidual p m f i a -
    henonResidual p m f i (s + a)

def henonDefectVector (p m : ℕ) (f : Fin m → HénonFp p → HénonFp p)
    (z a : HénonZ p m) : HénonB p m :=
  coordinateFunction p m f z + coordinateFunction p m f a -
    coordinateFunction p m f (z + a)

def henonDefectSpan (p m : ℕ) (f : Fin m → HénonFp p → HénonFp p)
    (z : HénonZ p m) : Submodule (HénonFp p) (HénonB p m) :=
  Submodule.span (HénonFp p) (Set.range (fun a => henonDefectVector p m f z a))

def finiteDifferenceContainmentClaim : Prop :=
  ∀ (p m : ℕ), Nat.Prime p ∧ Odd p ∧ 1 ≤ m →
    ∀ (f : Fin m → HénonFp p → HénonFp p),
      (∀ i, f i 0 = 0) →
        (∀ i s, henonResidual p m f i s ≠ 0 →
          s ≠ 0 ∧ ∃ a, henonDefect p m f i s a ≠ 0) ∧
        (∀ z, coordinateFunction p m f z - henonLinearPart p m f z ∈
          henonDefectSpan p m f z)





/-- Additive coordinates for C₂³ × C₉. -/
abbrev CayleyGroup := ZMod 2 × (ZMod 2 × (ZMod 2 × ZMod 9))

def cayleyAdjacency (S : Set CayleyGroup) (x y : CayleyGroup) : Prop :=
  x ≠ y ∧ y - x ∈ S

def cayleyConnected (S : Set CayleyGroup) : Prop :=
  ∀ x y, Relation.ReflTransGen (cayleyAdjacency S) x y

def ordinaryCayleyGraphIsomorphism (S T : Set CayleyGroup) : Prop :=
  ∃ e : CayleyGroup ≃ CayleyGroup,
    ∀ x y, cayleyAdjacency S x y ↔ cayleyAdjacency T (e x) (e y)

def inverseClosed (S : Set CayleyGroup) : Prop :=
  ∀ ⦃s⦄, s ∈ S → -s ∈ S

/-- Claim 59607: disconnected Cayley graphs on C₂³ × C₉ are CI-graphs. -/
def disconnectedCayleyCI : Prop :=
  ∀ S T : Set CayleyGroup,
    (∀ ⦃s⦄, s ∈ S → s ≠ (0 : CayleyGroup)) ∧
    (∀ ⦃t⦄, t ∈ T → t ≠ (0 : CayleyGroup)) →
    inverseClosed S →
    inverseClosed T →
    ordinaryCayleyGraphIsomorphism S T →
    ¬ cayleyConnected S →
    ∃ α : CayleyGroup ≃+ CayleyGroup,
      Set.image (fun g => α g) S = T





def finiteWindowOmega {I : Type*} (re im : I → ℝ) (m : I → ℤ) (T : ℝ)
    (i : I) : ℤ :=
  if 1 / 2 < re i ∧ |im i| < T then m i else 0

/-- Claim 59609: the support of each finite cutoff is exactly the right-of-wall support. -/
def finiteWindowSupportCharacterization : Prop :=
  ∀ (I : Type*) (re im : I → ℝ) (m : I → ℤ) (partner : I → I),
    (∀ i, m i ≠ 0) →
    (∀ i, re (partner i) = 1 - re i ∧
      |im (partner i)| = |im i|) →
    ∀ T : ℝ,
      (∀ i, finiteWindowOmega re im m T i = 0) ↔
        (∀ i, |im i| < T → re i = 1 / 2)



open MeasureTheory
open Topology
open scoped BigOperators


def primeTowerTerm (p k : ℕ) (t : ℝ) : ℂ :=
  (((Real.log (p : ℝ)) /
      Real.rpow (p : ℝ) (((k + 1 : ℕ) : ℝ) / 2)) : ℂ) *
    Complex.exp
      (-Complex.I * ((k + 1 : ℕ) : ℂ) * (t : ℂ) *
        (Real.log (p : ℝ) : ℂ))

def primeTower (p : ℕ) (t : ℝ) : ℂ :=
  ∑' k : ℕ, primeTowerTerm p k t

def primeTowerSum (P : Finset ℕ) (t : ℝ) : ℂ :=
  P.sum (fun p => primeTower p t)

def primeTowerR2 (P : Finset ℕ) : ℝ :=
  P.sum (fun p => (Real.log (p : ℝ)) ^ 2 / ((p : ℝ) - 1))

def primeTowerM (P : Finset ℕ) : ℝ :=
  P.sum (fun p => Real.log (p : ℝ) / (Real.sqrt (p : ℝ) - 1))

def primeTowerR (P : Finset ℕ) : ℝ :=
  Real.sqrt (primeTowerR2 P)

def primeTowerAmplitudeSet (P : Finset ℕ) (α : ℝ) : Set ℝ :=
  {t | 0 ≤ t ∧ α * primeTowerR P ≤ ‖primeTowerSum P t‖}

def lowerAsymptoticDensity (A : Set ℝ) : ℝ :=
  Filter.liminf
    (fun T : ℝ => ENNReal.toReal (volume (A ∩ Set.Icc 0 T)) / T) Filter.atTop

/-- Claim 59610: exact Cesàro energy and positive lower-density amplitudes. -/
def primeTowerCesaroEnergyClaim : Prop :=
  ∀ (P : Finset ℕ), P.Nonempty → (∀ p ∈ P, Nat.Prime p) →
    Filter.Tendsto
        (fun T : ℝ =>
          (∫ t in (0 : ℝ)..T, ‖primeTowerSum P t‖ ^ 2) / T)
        Filter.atTop (nhds (primeTowerR2 P)) ∧
      (∀ α : ℝ, 0 ≤ α → α < 1 →
        lowerAsymptoticDensity (primeTowerAmplitudeSet P α) ≥
            ((1 - α ^ 2) * primeTowerR2 P) /
              (primeTowerM P ^ 2 - α ^ 2 * primeTowerR2 P) ∧
          0 < ((1 - α ^ 2) * primeTowerR2 P) /
              (primeTowerM P ^ 2 - α ^ 2 * primeTowerR2 P))





abbrev CubeVector := Fin 2 → ℝ

def booleanCubeVector (v : CubeVector) : Prop :=
  ∀ i, v i = 0 ∨ v i = 1

def cubeHull : Set CubeVector :=
  {v | ∀ i, 0 ≤ v i ∧ v i ≤ 1}

def L₀ (v : CubeVector) : ℝ := 10 * (v 1) ^ 2
def L₁ (v : CubeVector) : ℝ := 10 * (v 0) ^ 2
def L₂ (v : CubeVector) : ℝ := 10 * (v 0 - v 1) ^ 2

def cubeVertexMinimum (v : CubeVector) : ℝ :=
  min (L₀ v) (min (L₁ v) (L₂ v))

def cubeVertex10 : CubeVector := ![1, 0]
def cubeVertex01 : CubeVector := ![0, 1]
def cubeInteriorPoint : CubeVector := ![1 / 3, 2 / 3]

def positiveSemidefiniteHomogeneous (L : CubeVector → ℝ) : Prop :=
  (∀ v, 0 ≤ L v) ∧
    (∀ (a : ℝ) v, L (a • v) = a ^ 2 * L v)

/-- Claim 59611: the three explicit PSD forms defeat vertex-only checking. -/
def psdVertexOnlyObstruction : Prop :=
  positiveSemidefiniteHomogeneous L₀ ∧
    positiveSemidefiniteHomogeneous L₁ ∧
    positiveSemidefiniteHomogeneous L₂ ∧
    (∀ v, booleanCubeVector v → cubeVertexMinimum v = 0) ∧
    (∀ v, booleanCubeVector v → cubeVertexMinimum v ≤ 1) ∧
    cubeInteriorPoint ∈ cubeHull ∧
    cubeInteriorPoint = (1 / 3 : ℝ) • cubeVertex10 +
      (2 / 3 : ℝ) • cubeVertex01 ∧
    L₀ cubeInteriorPoint = 40 / 9 ∧
    L₁ cubeInteriorPoint = 10 / 9 ∧
    L₂ cubeInteriorPoint = 10 / 9 ∧
    cubeVertexMinimum cubeInteriorPoint = 10 / 9 ∧
    cubeVertexMinimum cubeInteriorPoint > 1





/-- Claim 59613: endpoint sign patterns can be prescribed independently of a fixed nonreal zero. -/
def canonicalConeMorphismClaim : Prop :=
  ∀ (P : ℝ → ℝ) (F : ℂ → ℂ) (S : Set ℕ),
    P 0 ≠ 0 →
    (∃ z : ℂ, F z = 0 ∧ z.im ≠ 0) →
    ∃ H : ℕ → ContinuousMap ℝ ℝ,
      ∀ (N : ℕ) (y : ℝ),
        (0 ≤ H N (P (-y) / P 0)) ↔ N ∈ S

/-- Exact terminating-decimal constants from claim 59617. -/
def bridgeForwardMargin : ℝ := 0.0013129967192460183142
def bridgeMargin : ℝ := 0.000058093232689233683405437434725615050248801708221435546875
def bridgeTerminalMargin : ℝ := 0.009385823867106693485628209921570239

/-- Claim 59617: the independent perturbation radius is exactly the bridge margin. -/
def sharpPerturbationRadiusClaim : Prop :=
  ∀ ε : ℝ, 0 ≤ ε →
    (ε < bridgeMargin ↔
      ∀ δf δb δt : ℝ,
        |δf| ≤ ε → |δb| ≤ ε → |δt| ≤ ε →
          0 < bridgeForwardMargin + δf ∧
          0 < bridgeMargin + δb ∧
          0 < bridgeTerminalMargin + δt ∧
          bridgeMargin + δb < bridgeForwardMargin + δf ∧
          bridgeMargin + δb < bridgeTerminalMargin + δt)


end MathlibPlus.Open.ResearchFormalization
