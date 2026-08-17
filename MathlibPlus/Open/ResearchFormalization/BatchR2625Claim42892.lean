import MathlibPlus.Algebra.Claim42889
import MathlibPlus.Open.ResearchFormalizationBatch.Shell

namespace MathlibPlus.Open.ResearchFormalization.BatchR2625Claim42892

open scoped BigOperators
open MathlibPlus.Algebra.Claim42889
open MathlibPlus.Open.ResearchFormalizationBatch.Shell

noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Vec4 := Fin 4 → ℝ
abbrev Polarization (j : ℕ) :=
  MultilinearMap ℝ (fun _ : Fin j => Vec4) ℝ

def symmetricMultilinear {j : ℕ} (B : Polarization j) : Prop :=
  ∀ σ : Equiv.Perm (Fin j), ∀ v : Fin j → Vec4,
    B (v ∘ σ) = B v

def isPolarization {j : ℕ} (B : Polarization j) (D : Vec4 → ℝ) : Prop :=
  symmetricMultilinear B ∧
    ∀ t : Vec4, B (fun _ : Fin j => t) = D t

def uniquePolarization {j : ℕ} (B : Polarization j) (D : Vec4 → ℝ) : Prop :=
  isPolarization B D ∧
    ∀ C : Polarization j, isPolarization C D → C = B

def shellVector (n : ℕ) : Vec4 :=
  fun k => dividedShellMoment n k.val

def positiveTuple {j : ℕ} (n : Fin j → ℕ) : Prop :=
  ∀ i : Fin j, 1 ≤ n i

def tupleGcd {j : ℕ} (n : Fin j → ℕ) : ℕ :=
  Finset.gcd (Finset.univ : Finset (Fin j)) n

def gcdShellSummand {j : ℕ} (B : Polarization j) (d : ℕ)
    (n : Fin j → ℕ) : ℝ :=
  if positiveTuple n ∧ tupleGcd n = d then
    B (fun i => shellVector (n i))
  else 0

def gcdShellContribution {j : ℕ} (B : Polarization j) (d : ℕ) : ℝ :=
  ∑' n : Fin j → ℕ, gcdShellSummand B d n

def divisibleShellSummand (d : ℕ) (k : Fin 4) (n : ℕ) : ℝ :=
  if 1 ≤ n ∧ d ∣ n then shellVector n k else 0

def divisibleShellVector (d : ℕ) : Vec4 :=
  fun k => ∑' n : ℕ, divisibleShellSummand d k n

def divisibleExpansionSummand {j : ℕ} (B : Polarization j)
    (d r : ℕ) : ℝ :=
  if 1 ≤ r then gcdShellContribution B (d * r) else 0

def divisibleShellExpansion {j : ℕ} (B : Polarization j) (d : ℕ) : ℝ :=
  ∑' r : ℕ, divisibleExpansionSummand B d r

def mobiusReal (r : ℕ) : ℝ :=
  (ArithmeticFunction.moebius r : ℤ)

def mobiusSummand (D : Vec4 → ℝ) (d r : ℕ) : ℝ :=
  if 1 ≤ r then mobiusReal r * D (divisibleShellVector (d * r)) else 0

def mobiusExpansion (D : Vec4 → ℝ) (d : ℕ) : ℝ :=
  ∑' r : ℕ, mobiusSummand D d r

def wellFormedShellSums {j : ℕ} (B : Polarization j) (d : ℕ) : Prop :=
  (Summable (gcdShellSummand B d) ∧
    HasSum (gcdShellSummand B d) (gcdShellContribution B d)) ∧
    ∀ k : Fin 4,
      Summable (divisibleShellSummand d k) ∧
        HasSum (divisibleShellSummand d k) (divisibleShellVector d k)

def wellFormedExpansions {j : ℕ} (B : Polarization j)
    (D : Vec4 → ℝ) (d : ℕ) : Prop :=
  (Summable (divisibleExpansionSummand B d) ∧
    HasSum (divisibleExpansionSummand B d) (divisibleShellExpansion B d)) ∧
  (Summable (mobiusSummand D d) ∧
    HasSum (mobiusSummand D d) (mobiusExpansion D d))

/-- Homogeneous expansion over divisible shells and its integer Mobius
inversion, with all indexed series stated on their summable carriers. -/
def divisibleShellExpansionMobius_claim42892 : Prop :=
  ∃ (B₂ : Polarization 2) (B₃ : Polarization 3) (B₄ : Polarization 4),
    uniquePolarization B₂ determinantPiece₂ ∧
    uniquePolarization B₃ determinantPiece₃ ∧
    uniquePolarization B₄ determinantPiece₄ ∧
    ∀ d : ℕ, 1 ≤ d →
      wellFormedShellSums B₂ d ∧
      wellFormedShellSums B₃ d ∧
      wellFormedShellSums B₄ d ∧
      wellFormedExpansions B₂ determinantPiece₂ d ∧
      wellFormedExpansions B₃ determinantPiece₃ d ∧
      wellFormedExpansions B₄ determinantPiece₄ d ∧
      determinantPiece₂ (divisibleShellVector d) =
        divisibleShellExpansion B₂ d ∧
      determinantPiece₃ (divisibleShellVector d) =
        divisibleShellExpansion B₃ d ∧
      determinantPiece₄ (divisibleShellVector d) =
        divisibleShellExpansion B₄ d ∧
      gcdShellContribution B₂ d = mobiusExpansion determinantPiece₂ d ∧
      gcdShellContribution B₃ d = mobiusExpansion determinantPiece₃ d ∧
      gcdShellContribution B₄ d = mobiusExpansion determinantPiece₄ d

end
end MathlibPlus.Open.ResearchFormalization.BatchR2625Claim42892
