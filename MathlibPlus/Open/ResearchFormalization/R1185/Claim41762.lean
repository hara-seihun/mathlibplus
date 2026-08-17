import MathlibPlus.Open.Research.Q12PrimeCoverFormalization

namespace MathlibPlus.Open.ResearchFormalization.R1185

open MathlibPlus.Open.Research.Q12PrimeCover

/-- The two named generators in the presented `F₃⁺ ⋊ C₄` carrier. -/
def q12GeneratorX41762 : Q12Carrier := (1, 0)
def q12GeneratorY41762 : Q12Carrier := (0, 1)

/-- Inversion of the second and first displayed generators, respectively. -/
def q12InvertY41762 : Q12Carrier → Q12Carrier :=
  fun h => (h.1, -h.2)

def q12InvertX41762 : Q12Carrier → Q12Carrier :=
  fun h => (-h.1, h.2)

/-- A multiplication-preserving bijection of the displayed semidirect
carrier, with the images of its named generators made explicit. -/
def q12Automorphism41762
    (f : Q12Carrier → Q12Carrier)
    (xImage yImage : Q12Carrier) : Prop :=
  Function.Bijective f ∧
    f q12One = q12One ∧
      (∀ x y : Q12Carrier,
        f (q12Mul x y) = q12Mul (f x) (f y)) ∧
        f q12GeneratorX41762 = xImage ∧
          f q12GeneratorY41762 = yImage

/-- Conjugacy of the displayed switch with its inverse by an involutive
coordinate automorphism. -/
def q12SwitchConjugacy41762
    (f : Q12Carrier → Q12Carrier) : Prop :=
  Function.Involutive f ∧
    ∀ h : Q12Carrier,
      f (q12Switch (f h)) = q12SwitchInv h

/-- Claim 41762: the two concrete generator-inversion automorphisms conjugate
`σ` to `σ⁻¹` on the explicit `Q₁₂` carrier. -/
def claim41762 : Prop :=
  q12Automorphism41762 q12InvertY41762
    q12GeneratorX41762 (0, -1) ∧
    q12Automorphism41762 q12InvertX41762
      (-q12GeneratorX41762) q12GeneratorY41762 ∧
    q12SwitchConjugacy41762 q12InvertY41762 ∧
      q12SwitchConjugacy41762 q12InvertX41762

end MathlibPlus.Open.ResearchFormalization.R1185
