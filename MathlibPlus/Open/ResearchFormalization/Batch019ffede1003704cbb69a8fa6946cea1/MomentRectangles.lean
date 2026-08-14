import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Batch019ffede1003704cbb69a8fa6946cea1

noncomputable section

/-- The two-variable rational-function field denoted `Q(q,a)`. -/
abbrev MomentField := FractionRing (MvPolynomial (Fin 2) ℚ)

/-- A rooted-tree projective state line `ρ+xν` over the moment field. -/
def stateLine (rho nu : MomentField) : Polynomial MomentField :=
  Polynomial.C rho + Polynomial.X * Polynomial.C nu

/-- The scalar residual defect appearing after the simultaneous rectangle
identities. -/
def residualDefect
    (pA pB pC pD nuA nuB nuC nuD : MomentField) : MomentField :=
  (pA - nuA) * (pC - nuC) - (pB - nuB) * (pD - nuD)

/-- In the nonzero-`ν` chart, `[ρ:ν]` is represented by `ρ/ν`. -/
def projectiveStateChart (rho nu : MomentField) : MomentField :=
  rho / nu

/-- Claim 24138: a simultaneous `p/ν` rectangle has exactly one residual
state-line defect. -/
def claim_24138 : Prop :=
  ∀ (pA pB pC pD nuA nuB nuC nuD : MomentField),
    pA * pC = pB * pD →
      nuA * nuC = nuB * nuD →
        ∃ Ω : MomentField,
          Ω = residualDefect pA pB pC pD nuA nuB nuC nuD ∧
            stateLine (pA - nuA) nuA * stateLine (pC - nuC) nuC -
                stateLine (pB - nuB) nuB * stateLine (pD - nuD) nuD =
              Polynomial.C Ω * (Polynomial.C 1 - Polynomial.X)

/-- Claim 24139: zero residual defect forces equality of the two-element
multiset of projective states, expressed in the affine chart where every
second coordinate is nonzero. -/
def claim_24139 : Prop :=
  ∀ (pA pB pC pD nuA nuB nuC nuD Ω : MomentField),
    pA * pC = pB * pD →
      nuA * nuC = nuB * nuD →
        nuA ≠ 0 → nuB ≠ 0 → nuC ≠ 0 → nuD ≠ 0 →
          Ω = residualDefect pA pB pC pD nuA nuB nuC nuD →
            Ω = 0 →
              Multiset.cons (projectiveStateChart (pA - nuA) nuA)
                  (Multiset.cons (projectiveStateChart (pC - nuC) nuC) 0) =
                Multiset.cons (projectiveStateChart (pB - nuB) nuB)
                  (Multiset.cons (projectiveStateChart (pD - nuD) nuD) 0)

end

end MathlibPlus.Open.ResearchFormalization.Batch019ffede1003704cbb69a8fa6946cea1
