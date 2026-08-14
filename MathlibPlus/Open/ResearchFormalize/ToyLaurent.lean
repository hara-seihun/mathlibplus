import Mathlib

namespace MathlibPlus.Open.ResearchFormalizeBatch

abbrev ToyLabel := Fin 5

def p2 : ToyLabel := 0

def p3 : ToyLabel := 1

def g : ToyLabel := 2

def r : ToyLabel := 3

def t : ToyLabel := 4

abbrev ToyExponent := ToyLabel → ℤ
abbrev ToyLaurentAlgebra := MonoidAlgebra ℂ (Multiplicative ToyExponent)

/-- Claim 48172: the formal Laurent algebra on the five-symbol exponent lattice is a domain. -/
def claim_48172 : Prop := IsDomain ToyLaurentAlgebra

end MathlibPlus.Open.ResearchFormalizeBatch
