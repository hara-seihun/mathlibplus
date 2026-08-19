import Mathlib
import MathlibPlus.GraphTheory.CayleyCIHierarchy

namespace MathlibPlus.Open.ResearchFormalization.FullShearKernelClaim61340

universe u v

noncomputable section

/-- The independent fibre translation `(d,x) ↦ (d + f x,x)`. -/
def fibreShear {D H : Type*} [AddCommGroup D]
    (f : H → D) : Equiv.Perm (D × H) :=
  let swap : D × H ≃ H × D := Equiv.prodComm D H
  let sigma : (_h : H) × D ≃ H × D := Equiv.sigmaEquivProd H D
  let fibre : (_h : H) × D ≃ (_h : H) × D :=
    Equiv.sigmaCongrRight (fun h => Equiv.addRight (f h))
  swap.trans (sigma.symm.trans (fibre.trans (sigma.trans swap.symm)))

/-- Translation in the first coordinate of `D × H`. -/
def firstTranslation {D H : Type*} [AddCommGroup D]
    (d : D) : Equiv.Perm (D × H) :=
  Equiv.prodCongr (Equiv.addRight d) (Equiv.refl H)

/-- The literal lift of a permutation of the quotient coordinate. -/
def pureQuotientLift {D H : Type*}
    (sigma : Equiv.Perm H) : Equiv.Perm (D × H) :=
  Equiv.prodCongr (Equiv.refl D) sigma

/-- Binary two-closure membership for a set of permutations. -/
def binaryTwoClosureSet {α : Type*}
    (K : Set (Equiv.Perm α)) : Set (Equiv.Perm α) :=
  {q | ∀ x y : α, ∃ g : Equiv.Perm α,
    g ∈ K ∧ g x = q x ∧ g y = q y}

/-- The subgroup axioms for a set of permutations. -/
def isPermutationGroupSet {α : Type*}
    (K : Set (Equiv.Perm α)) : Prop :=
  (1 : Equiv.Perm α) ∈ K ∧
    (∀ g h : Equiv.Perm α, g ∈ K → h ∈ K → g * h ∈ K) ∧
      (∀ g : Equiv.Perm α, g ∈ K → g⁻¹ ∈ K)

/-- A permutation set is 2-closed when it contains its binary two-closure. -/
def isTwoClosedSet {α : Type*}
    (K : Set (Equiv.Perm α)) : Prop :=
  ∀ q : Equiv.Perm α, q ∈ binaryTwoClosureSet K → q ∈ K

/-- The induced action on the second-coordinate orbit set. -/
def inducedQuotientImage {D H : Type*}
    (K : Set (Equiv.Perm (D × H))) : Set (Equiv.Perm H) :=
  {sigma | ∃ g : Equiv.Perm (D × H), g ∈ K ∧
    ∀ d : D, ∀ x : H, (g (d, x)).2 = sigma x}

/-- Exact commutation with every first-coordinate translation. -/
def centralizesFirstTranslations {D H : Type*} [AddCommGroup D]
    (K : Set (Equiv.Perm (D × H))) : Prop :=
  ∀ g : Equiv.Perm (D × H), g ∈ K →
    ∀ d : D, g * firstTranslation d = firstTranslation d * g

/-- Semiregularity of the displayed translation action. -/
def firstTranslationSemiregular {D H : Type*} [AddCommGroup D] : Prop :=
  ∀ d : D, d ≠ 0 → ∀ z : D × H, firstTranslation d z ≠ z

/-- The all-finite full-shear quotient theorem, including the literal lift. -/
def fullShearKernelInducedQuotientClaim61340 : Prop :=
  ∀ (D : Type u) (H : Type v) [AddCommGroup D] [Fintype D] [Fintype H],
    ∀ (Y : Set (Equiv.Perm (D × H))),
      firstTranslationSemiregular (D := D) (H := H) →
      isPermutationGroupSet Y →
      isTwoClosedSet Y →
      centralizesFirstTranslations Y →
      (∀ f : H → D, fibreShear f ∈ Y) →
      ∀ sigma : Equiv.Perm H,
        sigma ∈ binaryTwoClosureSet (inducedQuotientImage Y) →
          sigma ∈ inducedQuotientImage Y ∧ pureQuotientLift sigma ∈ Y

/-- The relation of an additive Cayley graph. -/
def additiveCayleyRelation {G : Type*} [AddGroup G]
    (S : Set G) : Set (G × G) :=
  {p | p.2 - p.1 ∈ S}

/-- The full permutation automorphism set of a binary relation. -/
def relationAutomorphismSet {G : Type*}
    (R : Set (G × G)) : Set (Equiv.Perm G) :=
  {q | ∀ x y : G, (x, y) ∈ R ↔ (q x, q y) ∈ R}

/-- The centralizer of a set of permutations. -/
def centralizerSet {G : Type*}
    (K : Set (Equiv.Perm G)) : Set (Equiv.Perm G) :=
  {q | ∀ k : Equiv.Perm G, k ∈ K → q * k = k * q}

/-- Inverse closure for an additive connection set. -/
def inverseClosedAdditive {G : Type*} [AddGroup G]
    (S : Set G) : Prop :=
  ∀ x : G, x ∈ S ↔ -x ∈ S

/-- Identity-freeness for an additive connection set. -/
def identityFreeAdditive {G : Type*} [Zero G]
    (S : Set G) : Prop :=
  0 ∉ S

/-- Elementary abelianness in the prime-field additive chart. -/
def elementaryAbelianAdditive {H : Type*} [AddCommGroup H]
    (p : ℕ) : Prop :=
  ∀ x : H, p • x = 0

/-- Additive-subgroup closure for a period set. -/
def isAdditiveSubgroupSet {H : Type*} [AddCommGroup H]
    (P : Set H) : Prop :=
  0 ∈ P ∧
    (∀ x y : H, x ∈ P → y ∈ P → x + y ∈ P) ∧
      (∀ x : H, x ∈ P → -x ∈ P)

/-- The regular elementary-abelian permutation-copy conditions. -/
def regularElementaryAbelianCopy {Ω : Type*}
    (p : ℕ) (R : Set (Equiv.Perm Ω)) : Prop :=
  isPermutationGroupSet R ∧
    (∀ x y : Ω, ∃! r : Equiv.Perm Ω, r ∈ R ∧ r x = y) ∧
      (∀ r : Equiv.Perm Ω, r ∈ R → r ^ p = 1) ∧
        (∀ r s : Equiv.Perm Ω, r ∈ R → s ∈ R → r * s = s * r)

/-- A normalized pair with the common literal first-coordinate central line. -/
def normalizedCommonCentralPair {D H : Type*} [AddCommGroup D]
    (p : ℕ) (A R T : Set (Equiv.Perm (D × H))) : Prop :=
  regularElementaryAbelianCopy p R ∧
    regularElementaryAbelianCopy p T ∧
      R ⊆ A ∧ T ⊆ A ∧
        (∀ d : D, firstTranslation d ∈ R ∧ firstTranslation d ∈ T) ∧
          (∀ r : Equiv.Perm (D × H), r ∈ R →
            ∀ d : D, r * firstTranslation d = firstTranslation d * r) ∧
            (∀ t : Equiv.Perm (D × H), t ∈ T →
              ∀ d : D, t * firstTranslation d = firstTranslation d * t)

/-- Conjugacy of two permutation sets by an actual member of the ambient set. -/
def conjugatesInSet {Ω : Type*}
    (A R T : Set (Equiv.Perm Ω)) : Prop :=
  ∃ a : Equiv.Perm Ω, a ∈ A ∧
    ∀ r : Equiv.Perm Ω, r ∈ R ↔ a⁻¹ * r * a ∈ T

/-- The first-coordinate translation line in the prime-field Cayley chart. -/
def cayleyCentralLine {p : ℕ} {H : Type*} [AddCommGroup H] :
    Set (Equiv.Perm (ZMod p × H)) :=
  Set.range (fun d : ZMod p => firstTranslation d)

/-- The graph automorphism set in the prime-field Cayley chart. -/
def cayleyAutomorphismSet {p : ℕ} {H : Type*} [AddCommGroup H]
    (S : Set (ZMod p × H)) : Set (Equiv.Perm (ZMod p × H)) :=
  relationAutomorphismSet (additiveCayleyRelation S)

/-- The actual centralizer image used by the Cayley specialization. -/
def cayleyCentralizerSet {p : ℕ} {H : Type*} [AddCommGroup H]
    (S : Set (ZMod p × H)) : Set (Equiv.Perm (ZMod p × H)) :=
  cayleyAutomorphismSet S ∩ centralizerSet (cayleyCentralLine (p := p) (H := H))

/-- The pure shear kernel in the Cayley centralizer. -/
def cayleyShearCode {p : ℕ} {H : Type*} [AddCommGroup H]
    (S : Set (ZMod p × H)) : Set (H → ZMod p) :=
  {f | fibreShear f ∈ cayleyCentralizerSet S}

/-- The common period set of the Cayley shear code. -/
def cayleyPeriodSet {p : ℕ} {H : Type*} [AddCommGroup H]
    (S : Set (ZMod p × H)) : Set H :=
  {h | ∀ f : H → ZMod p, f ∈ cayleyShearCode S →
    ∀ x : H, f (x + h) = f x}

/-- A connection section above one quotient direction. -/
def cayleySection {p : ℕ} {H : Type*} [AddCommGroup H]
    (S : Set (ZMod p × H)) (h : H) : Set (ZMod p) :=
  {d | (d, h) ∈ S}

/-- The induced quotient image in the Cayley centralizer. -/
def cayleyQuotientImage {p : ℕ} {H : Type*} [AddCommGroup H]
    (S : Set (ZMod p × H)) : Set (Equiv.Perm H) :=
  inducedQuotientImage (cayleyCentralizerSet S)

/-- The Cayley specialization: the centralizer is 2-closed, the period code is
exactly the coset-constant code, and the full-kernel and saturation consequences
hold with the actual quotient image. -/
def cayleyCentralLineClaim61340 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (H : Type*) [AddCommGroup H] [Fintype H],
      elementaryAbelianAdditive (H := H) p →
        ∀ S : Set (ZMod p × H),
          inverseClosedAdditive S → identityFreeAdditive S →
            let A := cayleyAutomorphismSet S
            let Y := cayleyCentralizerSet S
            let M := cayleyShearCode S
            let P := cayleyPeriodSet S
            let Ybar := cayleyQuotientImage S
            isPermutationGroupSet A ∧
              isTwoClosedSet A ∧
                isPermutationGroupSet Y ∧
                  isTwoClosedSet Y ∧
                    firstTranslationSemiregular (D := ZMod p) (H := H) ∧
                      centralizesFirstTranslations Y ∧
                        isAdditiveSubgroupSet P ∧
                          M = {f | ∀ x h : H, h ∈ P → f (x + h) = f x} ∧
                      (P = ({0} : Set H) →
                        M = Set.univ ∧
                          ∀ sigma : Equiv.Perm H,
                            sigma ∈ binaryTwoClosureSet Ybar →
                              sigma ∈ Ybar ∧
                                pureQuotientLift sigma ∈ Y) ∧
                        (∀ h : H, h ∉ P →
                          cayleySection S h = (∅ : Set (ZMod p)) ∨
                            cayleySection S h = Set.univ) ∧
                          (∀ R T : Set (Equiv.Perm (ZMod p × H)),
                            normalizedCommonCentralPair p A R T →
                              MathlibPlus.GraphTheory.IsCayleyCI2
                                (Multiplicative H) →
                                P = ({0} : Set H) →
                                  conjugatesInSet A R T)

/-- In the normalized rank-six chart, a nonconjugate ordinary defect can occur
only in the nonzero-period residue. -/
def rankSixResidualClaim61340 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
    ∀ S : Set (ZMod p × (Fin 5 → ZMod p)),
      inverseClosedAdditive S → identityFreeAdditive S →
        let A := cayleyAutomorphismSet S
        let P := cayleyPeriodSet S
        ∀ R T : Set
            (Equiv.Perm (ZMod p × (Fin 5 → ZMod p))),
          normalizedCommonCentralPair p A R T →
            MathlibPlus.GraphTheory.IsCayleyCI2
              (Multiplicative (Fin 5 → ZMod p)) →
              ¬ conjugatesInSet A R T →
                P ≠ ({0} : Set (Fin 5 → ZMod p))

/-- Claim 61340: full independent fibre shears force actual quotient
2-closure, with the prime-field Cayley specialization and its exact residue. -/
def claim61340 : Prop :=
  fullShearKernelInducedQuotientClaim61340.{u, v} ∧
    cayleyCentralLineClaim61340.{u} ∧ rankSixResidualClaim61340

end

end MathlibPlus.Open.ResearchFormalization.FullShearKernelClaim61340
