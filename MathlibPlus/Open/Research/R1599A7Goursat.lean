import MathlibPlus.Open.Research.BatchR1599A7

noncomputable section

namespace MathlibPlus.Open.Research.R1599A7Goursat

abbrev Point7 := Fin 7
abbrev S7 := Equiv.Perm Point7
abbrev A7 := alternatingGroup Point7

def rho7 : S7 :=
  (((((Equiv.swap 0 1) * (Equiv.swap 1 2)) *
      (Equiv.swap 2 3)) * (Equiv.swap 3 4)) *
      (Equiv.swap 4 5)) * (Equiv.swap 5 6)

def conjugate7 (g s : S7) : S7 := s⁻¹ * g * s

def delta7 (σ : S7) : S7 :=
  rho7⁻¹ * conjugate7 rho7 σ

def derivativeTuple7 (σ : S7) (i : Fin 7) : S7 :=
  conjugate7 (delta7 σ) (rho7 ^ i.val)

def derivativeClosure7 (σ : S7) : Subgroup S7 :=
  Subgroup.closure (Set.range (derivativeTuple7 σ))

def a7Type7 (σ : S7) : Prop :=
  derivativeClosure7 σ = A7

def synchronousPairSubgroup7 (σ τ : S7) :
    Subgroup (S7 × S7) :=
  Subgroup.closure
    (Set.range (fun i : Fin 7 =>
      (derivativeTuple7 σ i, derivativeTuple7 τ i)))

def leftDerivativeClosure7 (σ : S7) : Subgroup S7 :=
  Subgroup.closure (Set.range (derivativeTuple7 σ))

def rightDerivativeClosure7 (τ : S7) : Subgroup S7 :=
  Subgroup.closure (Set.range (derivativeTuple7 τ))

def productA7Set7 : Set (S7 × S7) :=
  {p | p.1 ∈ A7 ∧ p.2 ∈ A7}

def automorphismGraphSet7 (α : MulAut A7) : Set (S7 × S7) :=
  {p | ∃ a : A7, p.1 = (a : S7) ∧ p.2 = ((α a : A7) : S7)}

def synchronousCarrier7 (σ τ : S7) : Set (S7 × S7) :=
  (synchronousPairSubgroup7 σ τ : Set (S7 × S7))

/-- Claim 39495: the two A₇-type derivative factors have the Goursat
full-product/automorphism-graph dichotomy. -/
def claim39495 : Prop :=
  ∀ σ τ : S7, σ ≠ τ → a7Type7 σ → a7Type7 τ →
    leftDerivativeClosure7 σ = A7 ∧
      rightDerivativeClosure7 τ = A7 ∧
      (synchronousCarrier7 σ τ = productA7Set7 ∨
        ∃ α : MulAut A7,
          synchronousCarrier7 σ τ = automorphismGraphSet7 α)

def tupleConjugates7 (σ τ s : S7) : Prop :=
  ∀ i : Fin 7,
    s⁻¹ * derivativeTuple7 σ i * s = derivativeTuple7 τ i

def rhoCentralizes7 (s : S7) : Prop :=
  s * rho7 = rho7 * s

def rhoPower7 (s : S7) : Prop :=
  ∃ k : Fin 7, s = rho7 ^ k.val

def chartConjugateBy7 (s σ : S7) : S7 :=
  s⁻¹ * σ * s

/-- Claim 39498: entrywise tuple conjugacy forces the conjugator to centralize
 the source seven-cycle. -/
def claim39498 : Prop :=
  ∀ σ τ s : S7,
    a7Type7 σ → a7Type7 τ → tupleConjugates7 σ τ s →
      rhoCentralizes7 s

/-- Claim 39499: the synchronous graph coupling is exactly the cyclic
centralizer, with the powers of the regular seven-cycle realizing the
couplings of a chart with its cycle-conjugates. -/
def claim39499 : Prop :=
  (∀ s : S7, rhoCentralizes7 s ↔ rhoPower7 s) ∧
    (∀ k : Fin 7, rhoPower7 (rho7 ^ k.val)) ∧
    (∀ σ τ : S7, a7Type7 σ → a7Type7 τ →
      ((∃ s : S7, tupleConjugates7 σ τ s) ↔
        ∃ k : Fin 7, tupleConjugates7 σ τ (rho7 ^ k.val))) ∧
    (∀ σ : S7, ∀ k : Fin 7,
      tupleConjugates7 σ
        (chartConjugateBy7 (rho7 ^ k.val) σ) (rho7 ^ k.val)) ∧
    (∀ s : S7, s ∉ A7 →
      ∀ σ τ : S7, a7Type7 σ → a7Type7 τ →
        ¬tupleConjugates7 σ τ s)

end MathlibPlus.Open.Research.R1599A7Goursat
