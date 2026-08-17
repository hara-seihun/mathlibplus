import MathlibPlus.Open.GraphTheory.AdmittedCubeFunctionInequalities

namespace MathlibPlus.Open.ResearchFormalization.EdgeCountConsequenceClaim35571

open Classical
open Filter
open Asymptotics
open MathlibPlus.Open.GraphTheory.AdmittedCubeFunctionInequalities

noncomputable section

abbrev EdgeSystem (n : ℕ) :=
  ∀ i : Fin n, F2Omega n i → Bool

abbrev EdgeSystemFamily := ∀ n : ℕ, EdgeSystem n

def translatedLiteral {n : ℕ} (f : EdgeSystem n) (i : Fin n)
    (v : F2Cube n) : F2Cube n → Bool :=
  fun x => f2EdgeAt f i (x + v)

def literalDirectionalOrbitSize {n : ℕ} (f : EdgeSystem n)
    (i : Fin n) : ℕ :=
  (Finset.univ.image (translatedLiteral f i)).card

def familyC4Free (F : EdgeSystemFamily) : Prop :=
  ∀ n : ℕ, f2C4Free (F n)

def familyOrbitBound (F : EdgeSystemFamily) (M : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) (i : Fin n), literalDirectionalOrbitSize (F n) i ≤ M n

def directionalMass (F : EdgeSystemFamily) (n : ℕ) : ℝ :=
  ∑ i : Fin n, f2Density (F n) i

def directionalEdgeCount (f : EdgeSystem n) (i : Fin n) : ℝ :=
  ∑ x : F2Omega n i, boolMass (f i x)

def edgeCount (F : EdgeSystemFamily) (n : ℕ) : ℝ :=
  ∑ i : Fin n, directionalEdgeCount (F n) i

def edgeMassIdentity (F : EdgeSystemFamily) : Prop :=
  ∀ n : ℕ,
    edgeCount F n = (2 : ℝ) ^ (n - 1) * directionalMass F n

def orbitLogCondition (M : ℕ → ℕ) : Prop :=
  IsLittleO atTop
    (fun n : ℕ => (M n : ℝ) * Real.log (M n : ℝ))
    (fun n : ℕ => Real.log (n : ℝ))

def logBaseTwo (x : ℝ) : ℝ :=
  Real.log x / Real.log 2

def explicitOrbitCondition (M : ℕ → ℕ) (ε : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    (M n : ℝ) ≤
      (1 / 2 - ε) * logBaseTwo (n : ℝ) /
        logBaseTwo (logBaseTwo (n : ℝ))

def littleEdgeFactor (F : EdgeSystemFamily) : Prop :=
  ∃ e : ℕ → ℝ,
    IsLittleO atTop e (fun _ : ℕ => (1 : ℝ)) ∧
      ∀ᶠ n : ℕ in atTop,
        edgeCount F n ≤
          ((1 / 2 : ℝ) + e n) * (n : ℝ) * (2 : ℝ) ^ (n - 1)

/-- The exact edge-count consequence for literal directional edge functions.
The declaration has no vertex-subset replacement and makes no assertion that
arbitrary edge functions admit a near-logarithmic approximation or a bounded
quotient rank. -/
def edgeCountConsequence_claim35571 : Prop :=
  ∀ (F : EdgeSystemFamily) (M : ℕ → ℕ),
    familyC4Free F →
      familyOrbitBound F M →
        (orbitLogCondition M ∨
          ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 ∧
            explicitOrbitCondition M ε) →
          edgeMassIdentity F ∧ littleEdgeFactor F

end
end MathlibPlus.Open.ResearchFormalization.EdgeCountConsequenceClaim35571
