import MathlibPlus.Open.GraphTheory.Q5x4Shears

namespace MathlibPlus.Open.ResearchFormalization.R2263

open MathlibPlus.Open.GraphTheory

/-- The displayed right-translate difference on the fixed `C₅ ⋊ C₄` carrier. -/
def difference43665 (φ : ShearQ → ShearF11)
    (h r : ShearQ) : ShearF11 :=
  φ r - φ (shearQMul r (shearQInv h))

/-- Right translation of a quotient function by the inverse of its translate. -/
def rightTranslate43665 (u : ShearQ)
    (f : ShearQ → ShearF11) : ShearQ → ShearF11 :=
  fun r => f (shearQMul r (shearQInv u))

/-- The `F₁₁`-span of all right translates of all displayed differences. -/
def differenceModule43665 (φ : ShearQ → ShearF11) :
    Submodule ShearF11 (ShearQ → ShearF11) :=
  Submodule.span ShearF11
    {f | ∃ h u : ShearQ,
      f = rightTranslate43665 u (difference43665 φ h)}

/-- The prescribed linear functional at a nonidentity quotient point. -/
def lambda43665 (q : ShearQ)
    (f : ShearQ → ShearF11) : ShearF11 :=
  f q - shearChi q * f shearQOne

/-- Claim 43665: the exact difference-module and defect-set definitions. -/
def defectSet43665 (φ : ShearQ → ShearF11) : Set ShearQ :=
  {q | q ≠ shearQOne ∧
    ∀ f, f ∈ differenceModule43665 φ → lambda43665 q f = 0}

end MathlibPlus.Open.ResearchFormalization.R2263
