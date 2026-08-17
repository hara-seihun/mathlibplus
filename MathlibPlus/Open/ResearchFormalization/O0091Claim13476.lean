import MathlibPlus.Open.ResearchFormalization.O0091Claim13482

open scoped BigOperators Matrix

namespace MathlibPlus.Open.ResearchFormalization.O0091Claim13476

noncomputable section

abbrev QMatrix := MathlibPlus.Open.ResearchFormalization.O0091Claim13482.QMatrix

/-- Pointwise composition of the concrete matrix operators. -/
def operatorCompose (F G : QMatrix → QMatrix) : QMatrix → QMatrix :=
  fun A => F (G A)

def operatorAdd (F G : QMatrix → QMatrix) : QMatrix → QMatrix :=
  fun A => F A + G A

def operatorScale (c : ℂ) (F : QMatrix → QMatrix) : QMatrix → QMatrix :=
  fun A => c • F A

def operatorZero : QMatrix → QMatrix := fun _ => 0

def operatorIdentity : QMatrix → QMatrix := fun A => A

def Epp : QMatrix → QMatrix :=
  fun A => MathlibPlus.Open.ResearchFormalization.O0091Claim13482.characterProjector 1 1 A

def Epm : QMatrix → QMatrix :=
  fun A => MathlibPlus.Open.ResearchFormalization.O0091Claim13482.characterProjector 1 (-1) A

def Emp : QMatrix → QMatrix :=
  fun A => MathlibPlus.Open.ResearchFormalization.O0091Claim13482.characterProjector (-1) 1 A

def Emm : QMatrix → QMatrix :=
  fun A => MathlibPlus.Open.ResearchFormalization.O0091Claim13482.characterProjector (-1) (-1) A

def characterProjectors : Fin 4 → QMatrix → QMatrix :=
  ![Epp, Epm, Emp, Emm]

def operatorRange (F : QMatrix → QMatrix) : Submodule ℂ QMatrix :=
  Submodule.span ℂ (Set.range F)

def characterSector (ε η : ℂ) : Set QMatrix :=
  {A | MathlibPlus.Open.ResearchFormalization.O0091Claim13482.S * A *
        MathlibPlus.Open.ResearchFormalization.O0091Claim13482.S = ε • A ∧
      MathlibPlus.Open.ResearchFormalization.O0091Claim13482.T * A *
        MathlibPlus.Open.ResearchFormalization.O0091Claim13482.T = η • A}

def simultaneousOrientationEven : Set QMatrix :=
  {A |
    MathlibPlus.Open.ResearchFormalization.O0091Claim13482.ST * A *
        MathlibPlus.Open.ResearchFormalization.O0091Claim13482.ST = A}

def operatorKernel (F : QMatrix → QMatrix) : Set QMatrix :=
  {A | F A = 0}

def singleFlipSum : Set QMatrix :=
  {A | ∃ B C : QMatrix,
    B ∈ characterSector (-1) 1 ∧
      C ∈ characterSector 1 (-1) ∧ A = B + C}

/-- The four character sectors, the channel multipliers, its semigroup law,
 and the nonzero-parameter range and kernel are stated on the concrete
 two-qubit matrix carrier. -/
def claim13476 : Prop :=
  (Module.finrank ℂ (operatorRange Epp) = 4 ∧
    Module.finrank ℂ (operatorRange Epm) = 4 ∧
    Module.finrank ℂ (operatorRange Emp) = 4 ∧
    Module.finrank ℂ (operatorRange Emm) = 4) ∧
  (∀ i j : Fin 4, i ≠ j →
    operatorCompose (characterProjectors i) (characterProjectors j) =
      operatorZero) ∧
  (operatorAdd (operatorAdd Epp Epm) (operatorAdd Emp Emm) =
    operatorIdentity) ∧
  (∀ lam : ℝ,
    MathlibPlus.Open.ResearchFormalization.O0091Claim13482.heat lam =
        operatorAdd Epp (operatorScale (lam : ℂ) Emm) ∧
      operatorCompose
          (MathlibPlus.Open.ResearchFormalization.O0091Claim13482.heat lam) Epp = Epp ∧
      operatorCompose
          (MathlibPlus.Open.ResearchFormalization.O0091Claim13482.heat lam) Epm =
        operatorZero ∧
      operatorCompose
          (MathlibPlus.Open.ResearchFormalization.O0091Claim13482.heat lam) Emp =
        operatorZero ∧
      operatorCompose
          (MathlibPlus.Open.ResearchFormalization.O0091Claim13482.heat lam) Emm =
        operatorScale (lam : ℂ) Emm) ∧
  (∀ lam mu : ℝ,
    operatorCompose
        (MathlibPlus.Open.ResearchFormalization.O0091Claim13482.heat lam)
        (MathlibPlus.Open.ResearchFormalization.O0091Claim13482.heat mu) =
      MathlibPlus.Open.ResearchFormalization.O0091Claim13482.heat (lam * mu)) ∧
  (∀ lam : ℝ, lam ≠ 0 →
    Set.range (MathlibPlus.Open.ResearchFormalization.O0091Claim13482.heat lam) =
        simultaneousOrientationEven ∧
      operatorKernel
          (MathlibPlus.Open.ResearchFormalization.O0091Claim13482.heat lam) =
        singleFlipSum)

end

end MathlibPlus.Open.ResearchFormalization.O0091Claim13476
