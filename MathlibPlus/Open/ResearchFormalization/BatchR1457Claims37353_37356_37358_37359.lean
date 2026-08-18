import Mathlib
import MathlibPlus.Open.ResearchFormalization.Batch1484

namespace MathlibPlus.Open.ResearchFormalization.BatchR1457

attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable section

abbrev H := MathlibPlus.Open.ResearchFormalization.Batch1484.H
abbrev W (d : ℕ) := MathlibPlus.Open.ResearchFormalization.Batch1484.W d

private def hInv (h : H) : H :=
  (-((2 : ZMod 7) ^ (-h.2).val) * h.1, -h.2)

private def fiberMul {d : ℕ} (a b : W d × H) : W d × H :=
  (a.1 +
      MathlibPlus.Open.ResearchFormalization.Batch1484.matchingScalarCharacter a.2 • b.1,
    MathlibPlus.Open.ResearchFormalization.Batch1484.hMul a.2 b.2)

private def fiberInv {d : ℕ} (a : W d × H) : W d × H :=
  (-(MathlibPlus.Open.ResearchFormalization.Batch1484.matchingScalarCharacter
      (hInv a.2) • a.1), hInv a.2)

private def affineProfile {d : ℕ}
    (lam : H → (ZMod 7)ˣ) (tau : H → W d) : W d × H → W d × H :=
  fun a => ((lam a.2 : ZMod 7) • a.1 + tau a.2, a.2)

private def affineProfileInv {d : ℕ}
    (lam : H → (ZMod 7)ˣ) (tau : H → W d) : W d × H → W d × H :=
  fun a => ((lam a.2 : ZMod 7)⁻¹ • (a.1 - tau a.2), a.2)

private def normalizedRelativeDerivative {d : ℕ}
    (lam : H → (ZMod 7)ˣ) (tau : H → W d)
    (g a : W d × H) : W d × H :=
  affineProfileInv lam tau
    (fiberMul
      (affineProfile lam tau (fiberMul a g))
      (fiberInv (affineProfile lam tau g)))

private def normalizedProfile {d : ℕ}
    (lam : H → (ZMod 7)ˣ) (tau : H → W d) : Prop :=
  lam (0, 0) = 1 ∧ tau (0, 0) = 0

private def relativeDerivativeValue {d : ℕ}
    (lam : H → (ZMod 7)ˣ) (tau : H → W d)
    (x : W d) (k h : H) (w : W d) : W d :=
  (lam h : ZMod 7)⁻¹ •
    ((lam (MathlibPlus.Open.ResearchFormalization.Batch1484.hMul h k) : ZMod 7) • w +
      (MathlibPlus.Open.ResearchFormalization.Batch1484.matchingScalarCharacter h *
          ((lam (MathlibPlus.Open.ResearchFormalization.Batch1484.hMul h k) : ZMod 7) -
            (lam k : ZMod 7))) • x +
      tau (MathlibPlus.Open.ResearchFormalization.Batch1484.hMul h k) -
        tau h -
        MathlibPlus.Open.ResearchFormalization.Batch1484.matchingScalarCharacter h • tau k)

private def relativeDerivativeMap {d : ℕ}
    (lam : H → (ZMod 7)ˣ) (tau : H → W d)
    (x : W d) (k h : H) : W d → W d :=
  fun w => (normalizedRelativeDerivative lam tau (x, k) (w, h)).1

private def leftPeriodSet (lam : H → (ZMod 7)ˣ) : Set H :=
  {h | ∀ k : H,
    (lam (MathlibPlus.Open.ResearchFormalization.Batch1484.hMul h k) : ZMod 7) =
      (lam k : ZMod 7)}

private def relativeDerivativeStep {d : ℕ}
    (lam : H → (ZMod 7)ˣ) (tau : H → W d) (h : H)
    (u v : W d) : Prop :=
  ∃ x : W d, ∃ k : H,
    relativeDerivativeMap lam tau x k h u = v

private def relativeDerivativeOrbit {d : ℕ}
    (lam : H → (ZMod 7)ˣ) (tau : H → W d) (h : H)
    (u : W d) : Set (W d) :=
  {v | Relation.ReflTransGen (relativeDerivativeStep lam tau h) u v}

private def hPow : ℕ → H → H
  | 0, _q => (0, 0)
  | n + 1, q =>
      MathlibPlus.Open.ResearchFormalization.Batch1484.hMul (hPow n q) q

private def cyclicSubset (Q : Set H) (q : H) : Prop :=
  Q = Set.range (fun n : ℕ => hPow n q)

private def defect {d : ℕ} (tau : H → W d) (h k : H) : W d :=
  tau (MathlibPlus.Open.ResearchFormalization.Batch1484.hMul h k) -
    tau h -
    MathlibPlus.Open.ResearchFormalization.Batch1484.matchingScalarCharacter h • tau k

private def defectSubspace {d : ℕ}
    (tau : H → W d) (Q : Set H) (q : H) : Submodule (ZMod 7) (W d) :=
  Submodule.span (ZMod 7)
    {v | ∃ k : H, k ∈ Q ∧ v = defect tau q k}

private def quotientCocycleOn {d : ℕ}
    (Q : Set H) (D : Submodule (ZMod 7) (W d))
    (z : H → (W d ⧸ D)) : Prop :=
  ∀ h k : H, h ∈ Q → k ∈ Q →
    z (MathlibPlus.Open.ResearchFormalization.Batch1484.hMul h k) =
      z h +
        MathlibPlus.Open.ResearchFormalization.Batch1484.matchingScalarCharacter h • z k

private def quotientLift {d : ℕ}
    (Q : Set H) (D : Submodule (ZMod 7) (W d))
    (z : H → (W d ⧸ D)) (zQ : H → W d) : Prop :=
  (∀ h : H, h ∈ Q → Submodule.mkQ D (zQ h) = z h) ∧
    (∀ h k : H, h ∈ Q → k ∈ Q →
      zQ (MathlibPlus.Open.ResearchFormalization.Batch1484.hMul h k) =
        zQ h +
          MathlibPlus.Open.ResearchFormalization.Batch1484.matchingScalarCharacter h • zQ k)

private def nonconstantMultiplier (lam : H → (ZMod 7)ˣ) : Prop :=
  ∃ x y : H, lam x ≠ lam y

private def fiberOrbit {d : ℕ}
    (lam : H → (ZMod 7)ˣ) (tau : H → W d) (h : H) (u : W d) : Set (W d × H) :=
  {a | a.2 = h ∧ a.1 ∈ relativeDerivativeOrbit lam tau h u}

private def cocycleAutomorphism {d : ℕ}
    (z : H → W d) : W d × H → W d × H :=
  fun a => (a.1 + z a.2, a.2)

private def isCocycleAutomorphism {d : ℕ}
    (z : H → W d) : Prop :=
  Function.Bijective (cocycleAutomorphism z) ∧
    ∀ a b : W d × H,
      cocycleAutomorphism z (fiberMul (a) b) =
        fiberMul (cocycleAutomorphism z a) (cocycleAutomorphism z b)

/-- Claim 37353: the normalized relative derivative on a W-fiber is the
exact displayed affine map. -/
def claim37353_exactRelativeDerivativeFormula : Prop :=
  ∀ (d : ℕ), 1 ≤ d →
    ∀ (lam : H → (ZMod 7)ˣ) (tau : H → W d),
      normalizedProfile lam tau →
      ∀ (x w : W d) (k h : H),
        normalizedRelativeDerivative lam tau (x, k) (w, h) =
          (relativeDerivativeValue lam tau x k h w, h)

/-- Claim 37356: outside the true left period, a nonzero coefficient gives
all pure fiber translations and the whole fiber is one derivative orbit. -/
def claim37356_saturationOutsideLeftPeriod : Prop :=
  ∀ (d : ℕ), 1 ≤ d →
    ∀ (lam : H → (ZMod 7)ˣ) (tau : H → W d) (h : H),
      normalizedProfile lam tau →
      h ∉ leftPeriodSet lam →
      ∃ k : H,
        (lam (MathlibPlus.Open.ResearchFormalization.Batch1484.hMul h k) : ZMod 7) ≠
          (lam k : ZMod 7) ∧
        ((lam h : ZMod 7)⁻¹ *
            MathlibPlus.Open.ResearchFormalization.Batch1484.matchingScalarCharacter h *
            ((lam (MathlibPlus.Open.ResearchFormalization.Batch1484.hMul h k) : ZMod 7) -
              (lam k : ZMod 7))) ≠ 0 ∧
        (∀ v : W d, ∃ x y : W d, ∀ u : W d,
          relativeDerivativeMap lam tau x k h u -
              relativeDerivativeMap lam tau y k h u = v) ∧
        (∀ u : W d, relativeDerivativeOrbit lam tau h u = Set.univ)

/-- Claim 37358: for a nontrivial cyclic left period, the cyclic defect
subspace yields quotient cocycles, lifts, and one global cocycle extension. -/
def claim37358_cyclicLocalDefectAndCocycleLift : Prop :=
  ∀ (d : ℕ), 1 ≤ d →
    ∀ (lam : H → (ZMod 7)ˣ) (tau : H → W d) (q : H),
      normalizedProfile lam tau →
      let Q := leftPeriodSet lam
      (∃ h : H, h ∈ Q ∧ h ≠ (0, 0)) →
      cyclicSubset Q q →
      let D := defectSubspace tau Q q
      let tauBar : H → (W d ⧸ D) := fun h => Submodule.mkQ D (tau h)
      (∀ h k : H, h ∈ Q → k ∈ Q → defect tau h k ∈ D) ∧
      quotientCocycleOn Q D tauBar ∧
      (∀ z : H → (W d ⧸ D), quotientCocycleOn Q D z →
        ∃ zQ : H → W d, quotientLift Q D z zQ) ∧
      (∃ zQ : H → W d,
        quotientLift Q D tauBar zQ ∧
        ∃ z : H → W d,
          MathlibPlus.Open.ResearchFormalization.Batch1484.isCocycle d z ∧
          (∀ h : H, h ∈ Q → z h = zQ h) ∧
          (∀ h : H, h ∈ Q → tau h - z h ∈ D))

/-- Claim 37359: every normalized nonconstant scalar-affine profile has one
global cocycle automorphism shadow on every relative-derivative orbit. -/
def claim37359_allDimensionalGlobalCocycleShadow : Prop :=
  ∀ (d : ℕ), 1 ≤ d →
    ∀ (lam : H → (ZMod 7)ˣ) (tau : H → W d),
      normalizedProfile lam tau →
      nonconstantMultiplier lam →
      ∃ z : H → W d,
        MathlibPlus.Open.ResearchFormalization.Batch1484.isCocycle d z ∧
        isCocycleAutomorphism z ∧
        (∀ (h : H) (u : W d),
          Set.image (affineProfile lam tau) (fiberOrbit lam tau h u) =
            Set.image (cocycleAutomorphism z) (fiberOrbit lam tau h u))

end

end MathlibPlus.Open.ResearchFormalization.BatchR1457
