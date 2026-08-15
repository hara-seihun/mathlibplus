import Mathlib

noncomputable section

namespace MathlibPlus.Open.Algebra.ConductorRees

abbrev Ambient := MvPolynomial (Option ℕ) ℚ

def sVar : Option ℕ := none

def zVar : Option ℕ := some 0

/-- The variables e₂,e₃,… occupy all `some (k - 1)` positions with `k ≥ 2`.
The `none` position is reserved for s and `some 0` for z. -/
def eVar (k : ℕ) : Option ℕ := some (k - 1)

def eIndex := {k : ℕ // 2 ≤ k}

def sPolynomialAlgebra : Subalgebra ℚ Ambient :=
  Algebra.adjoin ℚ {MvPolynomial.X sVar}

def conductorIdeal : Ideal Ambient :=
  Ideal.span (Set.range (fun k : eIndex => MvPolynomial.X (eVar k.1)))

def scalarAlgebra : Set Ambient :=
  {p | ∃ a k : Ambient,
    a ∈ sPolynomialAlgebra ∧ k ∈ conductorIdeal ∧ p = a + k}

def purePositiveZMonomial (n : ℕ) : Ambient :=
  MvPolynomial.X zVar ^ n

def scalarAlgebraPureZCharacterization : Prop :=
  ∀ p : Ambient,
    p ∈ scalarAlgebra ↔
      ∀ n : ℕ, 0 < n →
        MvPolynomial.coeff (Finsupp.single zVar n) p = 0

def conductorFiltration (n : ℕ) : Ideal Ambient := conductorIdeal ^ n

def conductorScalarAlgebraSetup : Prop :=
  scalarAlgebraPureZCharacterization

abbrev ReesPolynomial := Polynomial Ambient

def reesCarrier (P : ReesPolynomial) : Prop :=
  P.coeff 0 ∈ scalarAlgebra ∧
    ∀ n : ℕ, 0 < n → P.coeff n ∈ conductorFiltration n

def scalarConstants : Set ReesPolynomial :=
  {P | ∃ a : Ambient, a ∈ scalarAlgebra ∧ P = Polynomial.C a}

def reesGenerator (k : eIndex) (a : ℕ) : ReesPolynomial :=
  Polynomial.C (MvPolynomial.X zVar ^ a * MvPolynomial.X (eVar k.1)) * Polynomial.X

def reesGenerators : Set ReesPolynomial :=
  Set.range (fun ka : eIndex × ℕ => reesGenerator ka.1 ka.2)

def adjoinOverScalar (S : Set ReesPolynomial) : Subalgebra ℚ ReesPolynomial :=
  Algebra.adjoin ℚ (scalarConstants ∪ S)

def reesAlgebraGeneratedByExplicitFamily : Prop :=
  ∀ P : ReesPolynomial,
    reesCarrier P ↔ P ∈ adjoinOverScalar reesGenerators

def reesAlgebraNotFinitelyGenerated : Prop :=
  ¬ ∃ S : Set ReesPolynomial,
    S.Finite ∧
      ∀ P : ReesPolynomial,
        reesCarrier P ↔ P ∈ adjoinOverScalar S

end MathlibPlus.Open.Algebra.ConductorRees
