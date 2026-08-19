import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.FullClassShearLocalizationClaim61342

universe u v

noncomputable section

/-- Binary two-closure membership for a set of permutations. -/
def binaryTwoClosureSet {Ω : Type*}
    (Y : Set (Equiv.Perm Ω)) (q : Equiv.Perm Ω) : Prop :=
  ∀ x y : Ω, ∃ g : Equiv.Perm Ω,
    g ∈ Y ∧ g x = q x ∧ g y = q y

/-- The subgroup axioms for a permutation set. -/
def isPermutationGroupSet {Ω : Type*}
    (Y : Set (Equiv.Perm Ω)) : Prop :=
  (1 : Equiv.Perm Ω) ∈ Y ∧
    (∀ g h : Equiv.Perm Ω, g ∈ Y → h ∈ Y → g * h ∈ Y) ∧
      (∀ g : Equiv.Perm Ω, g ∈ Y → g⁻¹ ∈ Y)

/-- A permutation group is 2-closed for its coloured ordered orbitals. -/
def isTwoClosedSet {Ω : Type*}
    (Y : Set (Equiv.Perm Ω)) : Prop :=
  ∀ q : Equiv.Perm Ω, q ∈ Y ↔ binaryTwoClosureSet Y q

/-- Translation in the first coordinate of `D × H`. -/
def firstCoordinateTranslation {D H : Type*} [AddCommGroup D]
    (a : D) : Equiv.Perm (D × H) :=
  Equiv.prodCongr (Equiv.addRight a) (Equiv.refl H)

/-- Exact commutation with every first-coordinate translation. -/
def centralizesFirstTranslations {D H : Type*} [AddCommGroup D]
    (Y : Set (Equiv.Perm (D × H))) : Prop :=
  ∀ g : Equiv.Perm (D × H), g ∈ Y →
    ∀ a : D,
      g * firstCoordinateTranslation a =
        firstCoordinateTranslation a * g

/-- The unique fibre/base normal form asserted for every element of `Y`. -/
def hasUniqueFibreNormalForm {D H : Type*} [AddCommGroup D]
    (Y : Set (Equiv.Perm (D × H))) : Prop :=
  ∀ g : Equiv.Perm (D × H), g ∈ Y →
    ∃! p : (H → D) × Equiv.Perm H,
      ∀ d : D, ∀ x : H,
        g (d, x) = (d + p.1 x, p.2 x)

/-- The induced permutation image on the set of fibre-orbits. -/
def inducedQuotientImage {D H : Type*} [AddCommGroup D]
    (Y : Set (Equiv.Perm (D × H))) : Set (Equiv.Perm H) :=
  {sigma | ∃ g : Equiv.Perm (D × H), ∃ b : H → D,
    g ∈ Y ∧
      ∀ d : D, ∀ x : H,
        g (d, x) = (d + b x, sigma x)}

/-- The coloured ordered orbital relation of a permutation set. -/
def sameOrbital {Ω : Type*}
    (Y : Set (Equiv.Perm Ω)) (u v u' v' : Ω) : Prop :=
  ∃ g : Equiv.Perm Ω, g ∈ Y ∧ g u = u' ∧ g v = v'

/-- Membership of a raw map in a permutation set. -/
def functionInSet {Ω : Type*}
    (Y : Set (Equiv.Perm Ω)) (q : Ω → Ω) : Prop :=
  ∃ g : Equiv.Perm Ω, g ∈ Y ∧ ∀ u : Ω, g u = q u

/-- The relation `E` is an equivalence relation on the quotient coordinate. -/
def isEquivalenceRelation {H : Type*}
    (E : H → H → Prop) : Prop :=
  (∀ x : H, E x x) ∧
    (∀ x y : H, E x y → E y x) ∧
      (∀ x y z : H, E x y → E y z → E x z)

/-- Invariance of `E` under the induced quotient image. -/
def quotientRelationInvariant {H : Type*}
    (Ybar : Set (Equiv.Perm H)) (E : H → H → Prop) : Prop :=
  ∀ sigma : Equiv.Perm H, sigma ∈ Ybar →
    ∀ x y : H, E x y ↔ E (sigma x) (sigma y)

/-- The arbitrary fibre correction map in the theorem. -/
def quotientTransporter {D H : Type*} [Add D]
    (sigma : Equiv.Perm H) (c : H → D) : D × H → D × H :=
  fun u => (u.1 + c u.2, sigma u.2)

/-- `Y` contains every shear constant on the classes of `E`. -/
def containsClassConstantShears {D H : Type*} [AddCommGroup D]
    (Y : Set (Equiv.Perm (D × H))) (E : H → H → Prop) : Prop :=
  ∀ f : H → D,
    (∀ x y : H, E x y → f x = f y) →
      ∃ s : Equiv.Perm (D × H), s ∈ Y ∧
        ∀ d : D, ∀ x : H,
          s (d, x) = (d + f x, x)

/-- Every off-class pair is carried to its image by one `Y`-orbital. -/
def offClassOrbitalCondition {D H : Type*} [AddCommGroup D]
    (Y : Set (Equiv.Perm (D × H))) (E : H → H → Prop)
    (sigma : Equiv.Perm H) (c : H → D) : Prop :=
  ∀ d e : D, ∀ x y : H, ¬ E x y →
    sameOrbital Y (d, x) (e, y)
      (quotientTransporter sigma c (d, x))
      (quotientTransporter sigma c (e, y))

/-- Preservation of all orbitals on the same `E`-class pairs. -/
def sameClassOrbitalCondition {D H : Type*} [AddCommGroup D]
    (Y : Set (Equiv.Perm (D × H))) (E : H → H → Prop)
    (sigma : Equiv.Perm H) (c : H → D) : Prop :=
  ∀ d e : D, ∀ x y : H, E x y →
    sameOrbital Y (d, x) (e, y)
      (quotientTransporter sigma c (d, x))
      (quotientTransporter sigma c (e, y))

/-- An element of the quotient two-closure preserves the equivalence relation. -/
def preservesQuotientRelation {H : Type*}
    (E : H → H → Prop) (sigma : Equiv.Perm H) : Prop :=
  ∀ x y : H, E x y ↔ E (sigma x) (sigma y)

/-- The abstract full class-shear localization theorem. -/
def fullClassShearLocalization : Prop :=
  ∀ (D : Type u) (H : Type v) [AddCommGroup D] [Fintype D] [Fintype H],
    ∀ (Y : Set (Equiv.Perm (D × H))) (E : H → H → Prop),
      isPermutationGroupSet Y →
      isTwoClosedSet Y →
      centralizesFirstTranslations Y →
      isEquivalenceRelation E →
      quotientRelationInvariant (inducedQuotientImage Y) E →
      containsClassConstantShears Y E →
        (hasUniqueFibreNormalForm Y) ∧
          ∀ sigma : Equiv.Perm H,
            binaryTwoClosureSet (inducedQuotientImage Y) sigma →
              preservesQuotientRelation E sigma ∧
                (∀ c : H → D,
                  offClassOrbitalCondition Y E sigma c) ∧
                (∀ c : H → D,
                  functionInSet Y (quotientTransporter sigma c) ↔
                    sameClassOrbitalCondition Y E sigma c) ∧
                (sigma ∈ inducedQuotientImage Y ↔
                  ∃ c : H → D,
                    sameClassOrbitalCondition Y E sigma c)

/-- The ordinary additive Cayley adjacency used in the prime central-line
specialization. -/
def ordinaryCayleyAdjacency {G : Type*} [AddGroup G]
    (S : Set G) (x y : G) : Prop :=
  x ≠ y ∧ y - x ∈ S

/-- Identity-freeness and inverse-closedness of an undirected connection set. -/
def identityFree {G : Type*} [Zero G] (S : Set G) : Prop :=
  0 ∉ S

def inverseClosed {G : Type*} [Neg G] (S : Set G) : Prop :=
  ∀ x : G, x ∈ S ↔ -x ∈ S

/-- The automorphism set of the ordinary Cayley binary relation. -/
def ordinaryCayleyAutomorphisms {G : Type*} [AddGroup G]
    (S : Set G) : Set (Equiv.Perm G) :=
  {a | ∀ x y : G,
    ordinaryCayleyAdjacency S x y ↔
      ordinaryCayleyAdjacency S (a x) (a y)}

/-- The first-coordinate translation set in `F_p × H`. -/
def primeFirstCoordinateTranslations (p : ℕ) [Fact p.Prime]
    {H : Type*} [AddCommGroup H] :
    Set (Equiv.Perm (ZMod p × H)) :=
  {delta | ∃ a : ZMod p, ∀ d : ZMod p, ∀ x : H,
    delta (d, x) = (d + a, x)}

/-- The centralizer of the displayed translation set. -/
def permutationCentralizer {Ω : Type*}
    (K : Set (Equiv.Perm Ω)) : Set (Equiv.Perm Ω) :=
  {g | ∀ k : Equiv.Perm Ω, k ∈ K → g * k = k * g}

/-- The Cayley automorphism centralizer `Y`. -/
def primeCayleyCentralizer (p : ℕ) [Fact p.Prime]
    {H : Type*} [AddCommGroup H]
    (S : Set (ZMod p × H)) : Set (Equiv.Perm (ZMod p × H)) :=
  ordinaryCayleyAutomorphisms S ∩
    permutationCentralizer
      (primeFirstCoordinateTranslations (p := p) (H := H))

/-- Membership of the shear associated with a function in the actual centralizer. -/
def primeShearMember (p : ℕ) [Fact p.Prime]
    {H : Type*} [AddCommGroup H]
    (Y : Set (Equiv.Perm (ZMod p × H))) (f : H → ZMod p) : Prop :=
  ∃ s : Equiv.Perm (ZMod p × H), s ∈ Y ∧
    ∀ d : ZMod p, ∀ x : H,
      s (d, x) = (d + f x, x)

/-- The scalar shear function space and its common period set. -/
def primeShearSpace (p : ℕ) [Fact p.Prime]
    {H : Type*} [AddCommGroup H]
    (S : Set (ZMod p × H)) : Set (H → ZMod p) :=
  {f | primeShearMember p (primeCayleyCentralizer p S) f}

def primeCommonPeriod (p : ℕ) [Fact p.Prime]
    {H : Type*} [AddCommGroup H]
    (S : Set (ZMod p × H)) : Set H :=
  {h | ∀ f : H → ZMod p, f ∈ primeShearSpace p S →
    ∀ x : H, f (x + h) = f x}

/-- The induced quotient image and a connection section in the prime chart. -/
def primeQuotientImage (p : ℕ) [Fact p.Prime]
    {H : Type*} [AddCommGroup H]
    (S : Set (ZMod p × H)) : Set (Equiv.Perm H) :=
  inducedQuotientImage (primeCayleyCentralizer p S)

def primeSection (S : Set (ZMod p × H)) (h : H) : Set (ZMod p) :=
  {d | (d, h) ∈ S}

/-- The `P`-coset-constant scalar functions. -/
def constantOnPeriodCosets {p : ℕ} {H : Type*}
    [Fact p.Prime] [AddCommGroup H]
    (P : Set H) : Set (H → ZMod p) :=
  {f | ∀ x : H, ∀ h : H, h ∈ P → f (x + h) = f x}

/-- The elementary-abelian quotient hypothesis in the normalized chart. -/
def elementaryAbelianAtPrime {p : ℕ} [Fact p.Prime]
    {H : Type*} [AddCommGroup H] : Prop :=
  ∀ x : H, p • x = 0

/-- The complete prime central-line specialization, including the local gate,
its `P = 0` specialization, and section saturation outside `P`. -/
def primeCentralLineConsequence : Prop :=
  ∀ (p : ℕ) [Fact p.Prime]
    (H : Type*) [AddCommGroup H] [Fintype H],
    elementaryAbelianAtPrime (p := p) (H := H) →
      ∀ S : Set (ZMod p × H),
        identityFree S → inverseClosed S →
          let Y := primeCayleyCentralizer p S
          let M_Y := primeShearSpace p S
          let P := primeCommonPeriod p S
          let Ybar := primeQuotientImage p S
          let E : H → H → Prop := fun x y => y - x ∈ P
          isPermutationGroupSet Y ∧
            isTwoClosedSet Y ∧
              centralizesFirstTranslations Y ∧
                hasUniqueFibreNormalForm Y ∧
                  isEquivalenceRelation E ∧
                    quotientRelationInvariant Ybar E ∧
                      M_Y = constantOnPeriodCosets P ∧
                        containsClassConstantShears Y E ∧
                          (∀ sigma : Equiv.Perm H,
                            binaryTwoClosureSet Ybar sigma →
                              preservesQuotientRelation E sigma ∧
                                (∀ c : H → ZMod p,
                                  offClassOrbitalCondition Y E sigma c) ∧
                                (sigma ∈ Ybar ↔
                                  ∃ c : H → ZMod p,
                                    sameClassOrbitalCondition Y E sigma c)) ∧
                            (P = ({0} : Set H) →
                              (∀ sigma : Equiv.Perm H,
                                binaryTwoClosureSet Ybar sigma ↔
                                  sigma ∈ Ybar) ∧
                                (∀ sigma : Equiv.Perm H,
                                  binaryTwoClosureSet Ybar sigma →
                                    functionInSet Y
                                      (quotientTransporter sigma
                                        (fun _ : H => 0)))) ∧
                              (∀ h : H, h ∉ P →
                                primeSection S h = (∅ : Set (ZMod p)) ∨
                                  primeSection S h = Set.univ)

/-- Claim 61342: full class-shear kernels localize the actual quotient-image
criterion, with the prime central-line consequence. -/
def claim61342 : Prop :=
  fullClassShearLocalization.{u, v} ∧ primeCentralLineConsequence.{u}

end

end MathlibPlus.Open.ResearchFormalization.FullClassShearLocalizationClaim61342
