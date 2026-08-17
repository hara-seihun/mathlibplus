import MathlibPlus.Open.ResearchFormalizationBatch_01a004a9

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R1901Claims34789_34791

noncomputable section

abbrev Scalar := ZMod 2
abbrev Ambient (n : ℕ) := Fin n → Scalar
abbrev QuotientPlane := Fin 2 → Scalar

def coordinateProjection {n : ℕ} (i : Fin n) : Ambient n →ₗ[Scalar] Scalar :=
  LinearMap.proj i

abbrev Omega (n : ℕ) (i : Fin n) := (coordinateProjection i).ker
abbrev OmegaPair (n : ℕ) (i j : Fin n) := Omega n i ⊓ Omega n j

abbrev EdgeBase (n : ℕ) (i : Fin n) :=
  MathlibPlus.Open.ResearchFormalizationBatch.R1901.edgeBase n i

abbrev EdgeFunctions (n : ℕ) :=
  ∀ i : Fin n, EdgeBase n i → Fin 2


def basePoint {n : ℕ} {i : Fin n} (x : Omega n i) : EdgeBase n i :=
  ⟨x.1, x.2⟩

def omegaFunction {n : ℕ} {i : Fin n}
    (f : EdgeFunctions n) (x : Omega n i) : Fin 2 :=
  f i (basePoint x)

def omegaComplement {n : ℕ} {i : Fin n}
    (f : EdgeFunctions n) (x : Omega n i) : Bool :=
  decide (omegaFunction f x = 0)

def omegaComplementValue {n : ℕ} {i : Fin n}
    (f : EdgeFunctions n) (x : Omega n i) : ℕ :=
  if omegaComplement f x then 1 else 0

def omegaDensity {n : ℕ} {i : Fin n}
    (f : EdgeFunctions n) : ℝ :=
  letI : Fintype (Omega n i) := Fintype.ofFinite _
  (∑ x : Omega n i, (omegaComplementValue f x : ℝ)) /
    (Fintype.card (Omega n i) : ℝ)

def translateFunction {n : ℕ} {i : Fin n} {β : Type*}
    (g : Omega n i → β) (a : Omega n i) : Omega n i → β :=
  fun x => g (x + a)

def translationOrbit {n : ℕ} {i : Fin n} {β : Type*}
    (g : Omega n i → β) : Set (Omega n i → β) :=
  {h | ∃ a : Omega n i, h = translateFunction g a}

def omegaPairToI {n : ℕ} {i j : Fin n}
    (x : OmegaPair n i j) : Omega n i :=
  ⟨x.1, x.2.1⟩

def omegaPairToJ {n : ℕ} {i j : Fin n}
    (x : OmegaPair n i j) : Omega n j :=
  ⟨x.1, x.2.2⟩

def coordinateBasisInOmega {n : ℕ} {i j : Fin n}
    (e : Omega n i) : Prop :=
  e.1 = MathlibPlus.Open.ResearchFormalizationBatch.R1901.basisVector n j

def orbitFourContext {n : ℕ}
    (f : EdgeFunctions n) : Prop :=
  ∀ j : Fin n,
    Set.ncard (translationOrbit (omegaFunction f (i := j))) ≤ 4

def r1901Context {n : ℕ}
    (G : SimpleGraph (MathlibPlus.Open.ResearchFormalizationBatch.R1901.CubeVertex n))
    (f : EdgeFunctions n) (p : Fin n → ℝ) : Prop :=
  MathlibPlus.Open.ResearchFormalizationBatch.R1901.coordinateEdgeFunctionSetup
      n G f p ∧
    orbitFourContext f

def heavyAffineData {n : ℕ} {i : Fin n}
    (f : EdgeFunctions n)
    (F : Omega n i →ₗ[Scalar] QuotientPlane)
    (t : QuotientPlane) : Prop :=
  Function.Surjective F ∧
    omegaDensity (i := i) f = (1 : ℝ) / 4 ∧
      Set.ncard (translationOrbit (omegaComplement f (i := i))) = 4 ∧
        ∀ x : Omega n i,
          omegaComplementValue f x = 1 ↔ F x = t

/-- Claim 34789: under the exact C4-free coordinate-edge and translation-orbit
carrier, a 3/4-heavy direction has the density-one-quarter, orbit-four
complement and a surjective F2^2 affine quotient fibre. -/
def claim34789_heavyDirectionAffineQuotient : Prop :=
  ∀ (n : ℕ)
    (G : SimpleGraph
      (MathlibPlus.Open.ResearchFormalizationBatch.R1901.CubeVertex n))
    (f : EdgeFunctions n) (p : Fin n → ℝ) (i : Fin n),
    2 ≤ n →
      r1901Context G f p →
        p i = (3 : ℝ) / 4 →
          ∃ (F : Omega n i →ₗ[Scalar] QuotientPlane)
            (t : QuotientPlane),
            heavyAffineData f F t

/-- A nonzero alternating bilinear form on the quotient plane. -/
def isNonzeroAlternatingForm
    (B : QuotientPlane → QuotientPlane → Scalar) : Prop :=
  B ≠ 0 ∧
    (∀ x, B x x = 0) ∧
      (∀ x y z, B (x + y) z = B x z + B y z) ∧
        (∀ x y z, B x (y + z) = B x y + B x z) ∧
          (∀ a x y, B (a • x) y = a * B x y) ∧
            ∀ a x y, B x (a • y) = a * B x y

def squareMissingSum {n : ℕ} {i j : Fin n}
    (f : EdgeFunctions n) (eij : Omega n i) (eji : Omega n j)
    (x : OmegaPair n i j) : ℕ :=
  omegaComplementValue f (omegaPairToI x) +
    omegaComplementValue f (omegaPairToI x + eij) +
      omegaComplementValue f (omegaPairToJ x) +
        omegaComplementValue f (omegaPairToJ x + eji)

def iPairMissing {n : ℕ} {i j : Fin n}
    (f : EdgeFunctions n) (eij : Omega n i)
    (x : OmegaPair n i j) : Prop :=
  omegaComplementValue f (omegaPairToI x) +
      omegaComplementValue f (omegaPairToI x + eij) = 1

def jPairMissing {n : ℕ} {i j : Fin n}
    (f : EdgeFunctions n) (eji : Omega n j)
    (x : OmegaPair n i j) : Prop :=
  omegaComplementValue f (omegaPairToJ x) +
      omegaComplementValue f (omegaPairToJ x + eji) = 1

def iLambda {n : ℕ} {i j : Fin n}
    (B : QuotientPlane → QuotientPlane → Scalar)
    (F : Omega n i →ₗ[Scalar] QuotientPlane)
    (vij : QuotientPlane) (x : OmegaPair n i j) : Scalar :=
  B vij (F (omegaPairToI x))

def jLambda {n : ℕ} {i j : Fin n}
    (B : QuotientPlane → QuotientPlane → Scalar)
    (F : Omega n j →ₗ[Scalar] QuotientPlane)
    (vji : QuotientPlane) (x : OmegaPair n i j) : Scalar :=
  B vji (F (omegaPairToJ x))

def pairAffineConclusion {n : ℕ} {i j : Fin n}
    (f : EdgeFunctions n)
    (Fi : Omega n i →ₗ[Scalar] QuotientPlane) (ti : QuotientPlane)
    (Fj : Omega n j →ₗ[Scalar] QuotientPlane) (tj : QuotientPlane)
    (Bi : QuotientPlane → QuotientPlane → Scalar)
    (Bj : QuotientPlane → QuotientPlane → Scalar)
    (eij : Omega n i) (eji : Omega n j) : Prop :=
  let vij := Fi eij
  let vji := Fj eji
  let cij := Bi vij ti
  let cji := Bj vji tj
  vij ≠ 0 ∧
    vji ≠ 0 ∧
      (∀ x : OmegaPair n i j,
        1 ≤ squareMissingSum f eij eji x ∧
          squareMissingSum f eij eji x = 1) ∧
        (∀ x : OmegaPair n i j,
          iPairMissing f eij x ↔ iLambda Bi Fi vij x = cij) ∧
          (∀ x : OmegaPair n i j,
            jPairMissing f eji x ↔ jLambda Bj Fj vji x = cji) ∧
            (∀ x : OmegaPair n i j,
              iLambda Bi Fi vij x = jLambda Bj Fj vji x) ∧
              cij + cji = 1

/-- Claim 34790: the exact common-square one-missing-edge relation and its
paired affine hyperplanes, with the original edge, orbit, quotient, and
nonzero-displacement carriers retained. -/
def claim34790_heavyPairExactOneAffineHyperplanes : Prop :=
  ∀ (n : ℕ)
    (G : SimpleGraph
      (MathlibPlus.Open.ResearchFormalizationBatch.R1901.CubeVertex n))
    (f : EdgeFunctions n) (p : Fin n → ℝ) (i j : Fin n),
    2 ≤ n →
      r1901Context G f p →
        i ≠ j →
          p i = (3 : ℝ) / 4 →
            p j = (3 : ℝ) / 4 →
              ∀ (Fi : Omega n i →ₗ[Scalar] QuotientPlane)
                (ti : QuotientPlane)
                (Fj : Omega n j →ₗ[Scalar] QuotientPlane)
                (tj : QuotientPlane)
                (Bi : QuotientPlane → QuotientPlane → Scalar)
                (Bj : QuotientPlane → QuotientPlane → Scalar),
                heavyAffineData f Fi ti →
                  heavyAffineData f Fj tj →
                    isNonzeroAlternatingForm Bi →
                      isNonzeroAlternatingForm Bj →
                        ∃ (eij : Omega n i) (eji : Omega n j),
                          coordinateBasisInOmega (i := i) (j := j) eij ∧
                            coordinateBasisInOmega (i := j) (j := i) eji ∧
                              pairAffineConclusion
                                f Fi ti Fj tj Bi Bj eij eji

def heavyDirections {n : ℕ}
    (H : Finset (Fin n)) (t : Fin n → QuotientPlane) : Finset (Fin n) :=
  H.filter (fun i => t i ≠ 0)

def heavyFamilyData {n : ℕ}
    (G : SimpleGraph
      (MathlibPlus.Open.ResearchFormalizationBatch.R1901.CubeVertex n))
    (f : EdgeFunctions n) (p : Fin n → ℝ) (H : Finset (Fin n))
    (F : ∀ i : Fin n, Omega n i →ₗ[Scalar] QuotientPlane)
    (t : Fin n → QuotientPlane)
    (B : ∀ i : Fin n, QuotientPlane → QuotientPlane → Scalar)
    (e : ∀ i j : Fin n, Omega n i)
    (v : Fin n → Fin n → QuotientPlane)
    (c : Fin n → Fin n → Scalar) : Prop :=
  r1901Context G f p ∧
    (∀ i : Fin n, i ∈ H ↔ p i = (3 : ℝ) / 4) ∧
      (∀ i : Fin n, i ∈ H →
        heavyAffineData f (F i) (t i) ∧
          isNonzeroAlternatingForm (B i)) ∧
        (∀ i j : Fin n, i ∈ H → j ∈ H → i ≠ j →
          coordinateBasisInOmega (i := i) (j := j) (e i j) ∧
            coordinateBasisInOmega (i := j) (j := i) (e j i) ∧
              v i j = F i (e i j) ∧
                v j i = F j (e j i) ∧
                  c i j = B i (v i j) (t i) ∧
                    c j i = B j (v j i) (t j) ∧
                      pairAffineConclusion
                        f (F i) (t i) (F j) (t j)
                          (B i) (B j) (e i j) (e j i))

def tripleEqualityPattern {n : ℕ}
    (v : Fin n → Fin n → QuotientPlane)
    (i j k : Fin n) : Prop :=
  (v i j = v i k ↔ v j i = v j k) ∧
    (v j i = v j k ↔ v k i = v k j)

/-- Claim 34791: the common affine identity has one equality pattern on every
heavy triple; the induced nonzero-target tournament has no transitive triangle,
so at most three heavy targets are nonzero and at most four heavy directions
occur. -/
def claim34791_heavyTripleTournamentObstruction : Prop :=
  ∀ (n : ℕ)
    (G : SimpleGraph
      (MathlibPlus.Open.ResearchFormalizationBatch.R1901.CubeVertex n))
    (f : EdgeFunctions n) (p : Fin n → ℝ) (H : Finset (Fin n))
    (F : ∀ i : Fin n, Omega n i →ₗ[Scalar] QuotientPlane)
    (t : Fin n → QuotientPlane)
    (B : ∀ i : Fin n, QuotientPlane → QuotientPlane → Scalar)
    (e : ∀ i j : Fin n, Omega n i)
    (v : Fin n → Fin n → QuotientPlane)
    (c : Fin n → Fin n → Scalar),
    2 ≤ n →
      heavyFamilyData G f p H F t B e v c →
        let H₀ := heavyDirections H t
        (∀ i j k : Fin n,
          i ∈ H → j ∈ H → k ∈ H →
            i ≠ j → i ≠ k → j ≠ k →
              tripleEqualityPattern v i j k) ∧
          (H.filter (fun i => t i = 0)).card ≤ 1 ∧
            (∀ i j : Fin n,
              i ∈ H₀ → j ∈ H₀ → i ≠ j →
                c i j = 1 ∨ c i j = 0) ∧
              (∀ i j : Fin n,
                i ∈ H₀ → j ∈ H₀ → i ≠ j →
                  c i j + c j i = 1) ∧
              (∀ i j : Fin n,
                i ∈ H₀ → j ∈ H₀ → i ≠ j →
                  (c i j = 0 ↔ v i j = t i)) ∧
              (∀ i j k : Fin n,
                i ∈ H₀ → j ∈ H₀ → k ∈ H₀ →
                  i ≠ j → i ≠ k → j ≠ k →
                  ¬ (c i j = 1 ∧ c j k = 1 ∧ c i k = 1)) ∧
              H₀.card ≤ 3 ∧ H.card ≤ 4

end

end MathlibPlus.Open.ResearchFormalization.R1901Claims34789_34791
