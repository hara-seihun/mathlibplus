import Mathlib
import MathlibPlus.Open.PrimeFiber
import MathlibPlus.Open.Research.NormalizedFiniteAbelianVoltageShear

namespace MathlibPlus.Open.ResearchFormalization.R1402

noncomputable section

abbrev R1402Scalar := ZMod 3
abbrev R1402Base := Fin 5 → R1402Scalar
abbrev R1402FibreSpace := R1402Scalar × R1402Base
abbrev R1402GeneralLinear := LinearMap.GeneralLinearGroup R1402Scalar R1402Base

/-- The evaluation map on the actual quiet-point carrier. -/
def r1402Evaluation (Q : Set R1402Base) :
    (Q →₀ R1402Scalar) →ₗ[R1402Scalar] R1402Base :=
  Finsupp.linearCombination R1402Scalar (fun b : Q => (b : R1402Base))

/-- The relation space is the kernel of evaluation, with no replacement carrier. -/
def r1402RelationSpace (Q : Set R1402Base) :
    Submodule R1402Scalar (Q →₀ R1402Scalar) :=
  LinearMap.ker (r1402Evaluation Q)

/-- Pairing a finitely supported relation with a defect function. -/
def r1402RelationDefect {Q : Set R1402Base}
    (c : Q →₀ R1402Scalar) (d : Q → R1402Scalar) : R1402Scalar :=
  c.sum (fun b a => a * d b)

/-- The relation obtained from a linear automorphism of the quiet carrier. -/
def r1402TransportRelation {Q : Set R1402Base}
    (e : Q ≃ Q) : (Q →₀ R1402Scalar) →ₗ[R1402Scalar] (Q →₀ R1402Scalar) :=
  Finsupp.mapDomain.linearEquiv R1402Scalar R1402Scalar e

/-- The transported seed relations, using the restriction of the actual linear
automorphism to the actual quiet-point carrier. -/
def r1402GeneratedRelations
    (Q : Set R1402Base)
    (Γ : Subgroup R1402GeneralLinear)
    (S : Set (Q →₀ R1402Scalar)) : Set (Q →₀ R1402Scalar) :=
  {c | ∃ γ : Γ, ∃ c₀ : Q →₀ R1402Scalar,
      c₀ ∈ S ∧
        ∃ e : Q ≃ Q,
          (∀ b : Q, (e b : R1402Base) = γ.1.toLinearEquiv b) ∧
            c = r1402TransportRelation e c₀}

/-- The triangular section map used for the marked pair behind R-1402. -/
def r1402SectionMap (s : R1402Base → R1402Scalar)
    (g : Equiv.Perm R1402Base) : Equiv.Perm R1402FibreSpace :=
  (MathlibPlus.Open.voltageShear s).trans
    (Equiv.prodCongr (Equiv.refl R1402Scalar) g)

/-- The source translation copy and its transported target copy. -/
def r1402TranslationCopy : Subgroup (Equiv.Perm R1402FibreSpace) :=
  Subgroup.closure (Set.range (fun v : R1402FibreSpace => Equiv.addRight v))

def r1402TransportedTranslationCopy
    (s : R1402Base → R1402Scalar) (g : Equiv.Perm R1402Base) :
    Subgroup (Equiv.Perm R1402FibreSpace) :=
  r1402TranslationCopy.map
    (MulAut.conj (r1402SectionMap s g)).toMonoidHom

/-- The normalized projected derivative family behind the marked pair. -/
def r1402ProjectedDerivative (g : Equiv.Perm R1402Base)
    (k : R1402Base) : Equiv.Perm R1402Base :=
  (((Equiv.addRight k).trans g).trans
      (Equiv.addRight (-(g k)))).trans g.symm

def r1402ProjectedVoltage (s : R1402Base → R1402Scalar)
    (g : Equiv.Perm R1402Base) (k b : R1402Base) : R1402Scalar :=
  s (b + k) - s k - s (r1402ProjectedDerivative g k b)

/-- The base permutation used by an R-1402 candidate `gA`. -/
def r1402CandidateBaseGeneric {D B : Type*}
    [Semiring D] [AddCommMonoid B] [Module D B]
    (A : LinearMap.GeneralLinearGroup D B)
    (g : Equiv.Perm B) : Equiv.Perm B :=
  A.toLinearEquiv.toEquiv.trans g

def r1402CandidateBase (A : R1402GeneralLinear)
    (g : Equiv.Perm R1402Base) : Equiv.Perm R1402Base :=
  r1402CandidateBaseGeneric A g

/-- Additive circuits in a subspace, including the zero circuit. -/
def r1402AdditiveCircuitSpan (U : Submodule R1402Scalar R1402Base) : Prop :=
  let e0 : (U →₀ R1402Scalar) := Finsupp.single 0 1
  let circuits : Set (U →₀ R1402Scalar) :=
    {e0} ∪
      {c | ∃ x y : U,
        c = Finsupp.single x 1 + Finsupp.single y 1 -
          Finsupp.single (x + y) 1}
  r1402RelationSpace (U : Set R1402Base) =
    Submodule.span R1402Scalar circuits

/-- Claim 38643: the symmetry-generated relation criterion, its component and
potential transport hypotheses, its additive-circuit specialization, and the
independent-point case. -/
def symmetryGeneratedCircuitCriterion38643 : Prop :=
  let D := R1402Scalar
  let B := R1402Base
  ∀ (g : Equiv.Perm B) (s : B → D) (A : R1402GeneralLinear)
    (Q : Set B) (I : Type*) (C : I → Set B) (t : I → B → D)
    (iOf : Q → I) (qOf : Q → Q) (d : Q → D)
    (Γ : Subgroup R1402GeneralLinear) (S : Set (Q →₀ D)),
    let r := r1402ProjectedDerivative g
    let β := r1402ProjectedVoltage s g
    g 0 = 0 →
    s 0 = 0 →
    (∀ b : Q, (b : B) ∈ C (iOf b)) →
    (∀ b : B, b ∈ Q ↔ ∃ i : I, b ∈ C i) →
    (∀ b : Q, (qOf b : B) = r1402CandidateBase A g b) →
    (∀ γ : Γ, Set.image γ.1.toLinearEquiv Q = Q) →
    (∀ γ : Γ, ∀ i : I, ∃ j : I,
      Set.image γ.1.toLinearEquiv (C i) = C j ∧
        ∀ b, b ∈ C i → t j (γ.1.toLinearEquiv b) = t i b) →
    (∀ i : I, ∃ j : I,
      Set.image (r1402CandidateBase A g) (C i) = C j) →
    (∀ i : I, ∃ b₀ : B,
      MathlibPlus.Open.PrimeFiber.validPrimeFiberChoice
        r β (C i) b₀ ⊥ (t i)) →
    (∀ b : Q,
      d b = t (iOf (qOf b)) (qOf b) - t (iOf b) b -
        s (A.toLinearEquiv b)) →
    S ⊆ (r1402RelationSpace Q : Set (Q →₀ D)) →
    r1402RelationSpace Q =
      Submodule.span D (r1402GeneratedRelations Q Γ S) →
    (∀ c, c ∈ r1402GeneratedRelations Q Γ S →
      r1402RelationDefect c d = 0) →
    (∃ ell : B →ₗ[D] D, ∀ b : Q, ell b = d b) ∧
    (∀ U : Submodule D B,
      r1402AdditiveCircuitSpan U ∧
        ∀ h : B → D,
          h 0 = 0 →
          (∀ x y : U, h (x + y) = h x + h y) →
          ∃ ell : B →ₗ[D] D, ∀ x : U, ell x = h x) ∧
    (∀ Q' : Set B,
      LinearIndependent D (fun q : Q' => (q : B)) →
        r1402RelationSpace Q' = ⊥ ∧
          ∀ h : Q' → D, ∃ ell : B →ₗ[D] D, ∀ q : Q', ell q = h q)

/-- The identity-base derivative family. -/
def r1402IdentityRelativeDerivative (n : ℕ)
    (_u b : Fin n → ZMod 3) : Fin n → ZMod 3 := b

def r1402IdentityVoltage (n : ℕ) (s : (Fin n → ZMod 3) → ZMod 3)
    (u b : Fin n → ZMod 3) : ZMod 3 :=
  s (b + u) - s u - s b

def r1402IdentityDerivativeFamily (n : ℕ) :
    (Fin n → ZMod 3) → Equiv.Perm (Fin n → ZMod 3) :=
  fun _ => Equiv.refl (Fin n → ZMod 3)

def r1402IdentityVoltageFamily (n : ℕ)
    (s : (Fin n → ZMod 3) → ZMod 3) :
    (Fin n → ZMod 3) → (Fin n → ZMod 3) → ZMod 3 :=
  fun u b => r1402IdentityVoltage n s u b

def r1402IdentityQuietSet (n : ℕ)
    (s : (Fin n → ZMod 3) → ZMod 3) : Set (Fin n → ZMod 3) :=
  {b | ∀ x : Fin n → ZMod 3, s (b + x) = s b + s x}

def r1402IdentityPotential (n : ℕ) :
    (Fin n → ZMod 3) → ZMod 3 :=
  fun _ => 0

def r1402DefectFromPotential {D B : Type*}
    [Ring D] [AddCommMonoid B] [Module D B]
    (s : B → D) (g : Equiv.Perm B)
    (A : LinearMap.GeneralLinearGroup D B) (t : B → D)
    (b : B) : D :=
  t (r1402CandidateBaseGeneric A g b) - t b - s (A.toLinearEquiv b)

def r1402IdentityDefect (n : ℕ)
    (s : (Fin n → ZMod 3) → ZMod 3) :
    (Fin n → ZMod 3) → ZMod 3 :=
  fun b =>
    r1402DefectFromPotential s (Equiv.refl _) 1
      (r1402IdentityPotential n) b

def r1402IdentityNormalizerCorrection (n : ℕ)
    (s : (Fin n → ZMod 3) → ZMod 3)
    (ell : (Fin n → ZMod 3) →ₗ[ZMod 3] ZMod 3) :
    ZMod 3 × (Fin n → ZMod 3) → ZMod 3 × (Fin n → ZMod 3) :=
  fun x => (x.1 + ell x.2 + s x.2, x.2)

def r1402IdentityLinearRepairSet (n : ℕ)
    (s : (Fin n → ZMod 3) → ZMod 3) :
    Set ((Fin n → ZMod 3) →ₗ[ZMod 3] ZMod 3) :=
  {ell | ∀ b, b ∈ r1402IdentityQuietSet n s → ell b = -s b}

def r1402IdentityActualRepairSet (n : ℕ)
    (s : (Fin n → ZMod 3) → ZMod 3) :
    Set ((Fin n → ZMod 3) →ₗ[ZMod 3] ZMod 3) :=
  {ell | ∀ (a : ZMod 3) (b : Fin n → ZMod 3),
      Set.image (r1402IdentityNormalizerCorrection n s ell)
          (MathlibPlus.Open.voltagePointStabilizerOrbit s a b) =
        MathlibPlus.Open.voltagePointStabilizerOrbit s a b}

/-- Claim 38644: the identity-base class is stated on the actual prime-fiber
and point-stabilizer carriers, not on a definitionally replaced repair set. -/ 
def uniformIdentityBaseMarkedClass38644 : Prop :=
  ∀ (n : ℕ) (s : (Fin n → ZMod 3) → ZMod 3),
    s 0 = 0 →
    let B := Fin n → ZMod 3
    let r := r1402IdentityDerivativeFamily n
    let β := r1402IdentityVoltageFamily n s
    let Qs := r1402IdentityQuietSet n s
    (∀ u b, r1402IdentityRelativeDerivative n u b = b) ∧
    (∀ u b, β u b = s (b + u) - s u - s b) ∧
    (∀ b : B, MathlibPlus.Open.PrimeFiber.baseOrbit r b = {b}) ∧
    (∀ b : B, MathlibPlus.Open.PrimeFiber.primeFiberQuietPoint r β b ↔ b ∈ Qs) ∧
    (∀ b : B, b ∈ Qs →
      MathlibPlus.Open.PrimeFiber.validPrimeFiberChoice r β {b} b ⊥
        (fun _ : B => 0)) ∧
    MathlibPlus.Open.PrimeFiber.preservesEveryPrimeFiberComponent r
      (Equiv.refl B) ∧
    (∀ b : B, b ∈ Qs → r1402IdentityDefect n s b = -s b) ∧
    (∀ b : B, b ∈ Qs → r1402IdentityPotential n b = 0) ∧
    (r1402IdentityActualRepairSet n s = r1402IdentityLinearRepairSet n s) ∧
    ∃ Q : Submodule (ZMod 3) B,
      (∀ b : B, b ∈ Q ↔ b ∈ Qs) ∧
      (∀ x y : B, x ∈ Q → y ∈ Q → s (x + y) = s x + s y) ∧
      (∃ ell : B →ₗ[ZMod 3] ZMod 3,
        ∀ b : B, b ∈ Q → ell b = -s b) ∧
      Nat.card {ell : B →ₗ[ZMod 3] ZMod 3 //
        ell ∈ r1402IdentityActualRepairSet n s} =
        3 ^ (n - Module.finrank (ZMod 3) Q)

end

end MathlibPlus.Open.ResearchFormalization.R1402
