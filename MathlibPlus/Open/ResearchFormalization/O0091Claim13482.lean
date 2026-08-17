import Mathlib

open scoped BigOperators Matrix

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.O0091Claim13482

abbrev Qubit := Fin 2
abbrev QIndex := Qubit × Qubit
abbrev LocalMatrix := Matrix Qubit Qubit ℂ
abbrev QMatrix := Matrix QIndex QIndex ℂ

def pauliI : LocalMatrix := 1

def pauliX : LocalMatrix := !![0, 1; 1, 0]

def tensor (A B : LocalMatrix) : QMatrix := Matrix.kronecker A B

def S : QMatrix := tensor pauliX pauliI

def T : QMatrix := tensor pauliI pauliX

def ST : QMatrix := S * T

def heat (lam : ℝ) (A : QMatrix) : QMatrix :=
  (((1 + lam) / 4 : ℝ) : ℂ) •
      (A + ST * A * ST)
    + (((1 - lam) / 4 : ℝ) : ℂ) •
      (S * A * S + T * A * T)

def characterProjector (ε η : ℂ) (A : QMatrix) : QMatrix :=
  (1 / 4 : ℂ) •
    (A + ε • (S * A * S) + η • (T * A * T) +
      (ε * η) • (ST * A * ST))

def heatMoorePenroseCandidate (lam : ℝ) (A : QMatrix) : QMatrix :=
  characterProjector 1 1 A +
    ((lam⁻¹ : ℝ) : ℂ) • characterProjector (-1) (-1) A

def hilbertSchmidt (A B : QMatrix) : ℂ :=
  ∑ i, ∑ j, star (A i j) * B i j

def moorePenroseInverse (F G : QMatrix → QMatrix) : Prop :=
  (∀ A, F (G (F A)) = F A) ∧
    (∀ A, G (F (G A)) = G A) ∧
    (∀ A B, hilbertSchmidt (F (G A)) B = hilbertSchmidt A (F (G B))) ∧
    (∀ A B, hilbertSchmidt (G (F A)) B = hilbertSchmidt A (G (F B)))

/-- The concrete character-sector Moore--Penrose inverse, its Penrose
characterization and its exact half-heat formula. -/
def claim13482 : Prop :=
  (∀ (lam : ℝ), lam ≠ 0 →
    moorePenroseInverse (heat lam) (heatMoorePenroseCandidate lam) ∧
      (∀ G : QMatrix → QMatrix,
        moorePenroseInverse (heat lam) G →
          G = heatMoorePenroseCandidate lam) ∧
      (∀ A : QMatrix,
        heat lam (heatMoorePenroseCandidate lam A) = heat 1 A ∧
          heatMoorePenroseCandidate lam (heat lam A) = heat 1 A)) ∧
  (∀ A : QMatrix,
    heatMoorePenroseCandidate (1 / 2 : ℝ) A =
      (1 / 4 : ℂ) •
        (3 • A - S * A * S - T * A * T + 3 • (ST * A * ST)))

end MathlibPlus.Open.ResearchFormalization.O0091Claim13482
