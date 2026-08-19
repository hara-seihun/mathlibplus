import Mathlib

/-!
Exact open propositions for the four admitted R-1349 diagonal-strip steps.
-/

namespace MathlibPlus.Open.GroupTheory.R1349Claims41238_41242

abbrev C7 := Multiplicative (ZMod 7)
abbrev Q12 := QuaternionGroup 3
abbrev A12 := (Equiv.Perm.sign : Equiv.Perm (Fin 12) →* ℤˣ).ker
abbrev Base := Fin 7 → Equiv.Perm (Fin 12)
abbrev Ω := Fin 7 × Fin 12

/-- The actual alternating subgroup in every coordinate of the base. -/
def alternatingPowerSet : Set Base :=
  {g | ∀ i : Fin 7, g i ∈ A12}

/-- The local image of a global block-kernel subgroup in one block. -/
def localImage (H : Subgroup Base) (i : Fin 7) :
    Set (Equiv.Perm (Fin 12)) :=
  {p | ∃ h : H, p = h.1 i}

/-- A local permutation implements the fixed global isomorphism on one block. -/
def localTransporter
    (N M : Subgroup Base) (θ : N ≃* M) (i : Fin 7)
    (p : Equiv.Perm (Fin 12)) : Prop :=
  ∀ n : N, ∀ x : Fin 12,
    p ((n : Base) i x) = ((θ n : M) : Base) i (p x)

/-- The precise coset interface for the local transporter set. -/
def localTransporterCoset
    (N M : Subgroup Base) (θ : N ≃* M) : Prop :=
  ∀ i : Fin 7, ∃ t : Equiv.Perm (Fin 12),
    localTransporter N M θ i t ∧
      ∀ p : Equiv.Perm (Fin 12),
        localTransporter N M θ i p ↔
          ∃ c : Equiv.Perm (Fin 12),
            c ∈ Subgroup.centralizer (localImage M i) ∧ p = t * c

/-- A global Q12 kernel may have arbitrary, not necessarily diagonal,
coordinate images; each coordinate action is required to be regular. -/
def globalQ12Kernel (N : Subgroup Base) : Prop :=
  Nonempty (N ≃* Q12) ∧
    ∀ i : Fin 7, ∀ x y : Fin 12,
      ∃! n : N, (n : Base) i x = y

/-- The parity fact supplied by the opposite regular centralizer on every
block. -/
def oddLocalCentralizers
    (M : Subgroup Base) : Prop :=
  ∀ i : Fin 7, ∃ c : Equiv.Perm (Fin 12),
    c ∈ Subgroup.centralizer (localImage M i) ∧
      Equiv.Perm.sign c ≠ 1

/-- Equality of global kernels after blockwise conjugation. -/
def conjugatesGlobalKernel
    (N M : Subgroup Base) (g : Base) : Prop :=
  ∀ x : Base, x ∈ M ↔
    ∃ n : N, x = g * (n : Base) * g⁻¹

/-- Claim 41238: the full product branch is explicitly K'=A12^7, while
N and M remain arbitrary global regular-Q12 kernels. -/
def claim41238 : Prop :=
  ∀ (Kprime N M : Subgroup Base) (θ : N ≃* M),
    (Kprime : Set Base) = alternatingPowerSet →
    globalQ12Kernel N →
    globalQ12Kernel M →
    localTransporterCoset N M θ →
    oddLocalCentralizers M →
    ∃ g : Base,
      (∀ i : Fin 7, Equiv.Perm.sign (g i) = 1) ∧
        g ∈ Kprime ∧
          conjugatesGlobalKernel N M g

/-- A block of the actual 84-point imprimitive carrier. -/
def block (i : Fin 7) : Set Ω :=
  {x | x.1 = i}

/-- The literal diagonal permutation in the 84-point carrier. -/
def diagonalFull (s : Equiv.Perm (Fin 12)) : Equiv.Perm Ω :=
  Equiv.prodCongr (Equiv.refl (Fin 7)) s

/-- A permutation of the seven blocks, with no local component. -/
def blockPermutation (σ : Equiv.Perm (Fin 7)) : Equiv.Perm Ω :=
  Equiv.prodCongr σ (Equiv.refl (Fin 12))

/-- Exact carrier predicate for the full imprimitive wreath product. -/
def fullImprimitiveWreath
    (W : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ w : Equiv.Perm Ω, w ∈ W ↔
    ∀ i : Fin 7, ∃ j : Fin 7, w '' block i = block j

/-- The literal diagonal A12 strip in the base carrier. -/
def diagonalA12BaseSet : Set Base :=
  {g | ∃ a : A12, ∀ i : Fin 7, g i = (a : Equiv.Perm (Fin 12))}

/-- The literal diagonal A12 strip in the full imprimitive carrier. -/
def diagonalA12FullSet : Set (Equiv.Perm Ω) :=
  Set.range (fun a : A12 => diagonalFull (a : Equiv.Perm (Fin 12)))

/-- Untwisting is recorded as conjugacy by an actual base permutation. -/
def baseStripUntwisted
    (S D : Subgroup Base) : Prop :=
  ∃ u : Base, ∀ x : Base,
    x ∈ S ↔ ∃ d : D, x = u * (d : Base) * u⁻¹

/-- The form of the direct-product normalizer in the full carrier. -/
def wreathDirectProductForm (g : Equiv.Perm Ω) : Prop :=
  ∃ s : Equiv.Perm (Fin 12), ∃ σ : Equiv.Perm (Fin 7),
    g = diagonalFull s * blockPermutation σ

/-- A subgroup is a block kernel when it lies in the wreath carrier and fixes
all seven blocks setwise. -/
def blockKernelInWreath
    (K W : Subgroup (Equiv.Perm Ω)) : Prop :=
  K ≤ W ∧
    ∀ k : K, ∀ i : Fin 7,
      (k : Equiv.Perm Ω) '' block i = block i

/-- Claim 41240: the diagonal A12 strip is untwisted first; its base and
full-wreath normalizers are then the literal diagonal S12 and its direct
product with S7, with the block-kernel consequence stated explicitly. -/
def claim41240 : Prop :=
  ∀ (S D : Subgroup Base)
    (W E K : Subgroup (Equiv.Perm Ω)),
    (D : Set Base) = diagonalA12BaseSet →
    baseStripUntwisted S D →
    fullImprimitiveWreath W →
    (E : Set (Equiv.Perm Ω)) = diagonalA12FullSet →
    blockKernelInWreath K W →
    K ≤ Subgroup.normalizer (E : Set (Equiv.Perm Ω)) →
    (∀ g : Base, g ∈ Subgroup.normalizer (D : Set Base) ↔
      ∃ s : Equiv.Perm (Fin 12), ∀ i : Fin 7, g i = s) ∧
      (∀ g : Equiv.Perm Ω, g ∈ W →
        (g ∈ Subgroup.normalizer (E : Set (Equiv.Perm Ω)) ↔
          wreathDirectProductForm g)) ∧
        (∀ k : K, ∃ s : Equiv.Perm (Fin 12),
          (k : Equiv.Perm Ω) = diagonalFull s)

/-- Regularity of an actual twelve-point Q12 permutation subgroup. -/
def regularQ12Action
    (N : Subgroup (Equiv.Perm (Fin 12))) : Prop :=
  Nonempty (N ≃* Q12) ∧
    ∀ x y : Fin 12, ∃! n : N, (n : Equiv.Perm (Fin 12)) x = y

/-- The order-twelve centralizer fact used to eliminate a diagonal
component. -/
def q12CentralizerOrderData
    (N : Subgroup (Equiv.Perm (Fin 12))) : Prop :=
  Nat.card (Subgroup.centralizer (N : Set (Equiv.Perm (Fin 12)))) = 12 ∧
    ∀ c : Equiv.Perm (Fin 12),
      c ∈ Subgroup.centralizer (N : Set (Equiv.Perm (Fin 12))) →
        c ^ 7 = 1 → c = 1

/-- A regular block seven-cycle. -/
def regularBlockSevenCycle (σ : Equiv.Perm (Fin 7)) : Prop :=
  orderOf σ = 7 ∧
    ∀ i j : Fin 7, ∃ n : ℕ, (σ ^ n) i = j

/-- A complement P has a C7 model, lies in the imprimitive wreath carrier,
and centralizes the diagonal lift of its regular Q12 kernel. -/
def diagonalStripC7Complement
    (P W : Subgroup (Equiv.Perm Ω))
    (N : Subgroup (Equiv.Perm (Fin 12))) : Prop :=
  P ≤ W ∧
    Nonempty (P ≃* C7) ∧
      ∀ p : P, ∀ n : N,
        Commute (p : Equiv.Perm Ω)
          (diagonalFull (n : Equiv.Perm (Fin 12)))

/-- Claim 41241: seventh-power triviality is the conclusion of the
commuting factorization and order-seven hypotheses, not an input. -/
def claim41241 : Prop :=
  ∀ (W P : Subgroup (Equiv.Perm Ω))
    (N : Subgroup (Equiv.Perm (Fin 12)))
    (p : Equiv.Perm Ω) (s : Equiv.Perm (Fin 12))
    (σ : Equiv.Perm (Fin 7)),
    fullImprimitiveWreath W →
    regularQ12Action N →
    q12CentralizerOrderData N →
    diagonalStripC7Complement P W N →
    p ∈ P →
    Subgroup.closure ({p} : Set (Equiv.Perm Ω)) = P →
    regularBlockSevenCycle σ →
    p = diagonalFull s * blockPermutation σ →
    Commute (diagonalFull s) (blockPermutation σ) →
    orderOf p = 7 →
    s ^ 7 = 1 ∧
      s ∈ Subgroup.centralizer (N : Set (Equiv.Perm (Fin 12))) ∧
        s = 1

/-- The pointwise block action induced by a permutation. -/
def inducesBlockPermutation
    (g : Equiv.Perm Ω) (σ : Equiv.Perm (Fin 7)) : Prop :=
  ∀ i : Fin 7, ∀ x : Fin 12,
    (g (i, x)).1 = σ i

/-- The quotient subgroup on the seven blocks, represented in its actual
permutation carrier. -/
def blockQuotientSet
    (H : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm (Fin 7)) :=
  {σ | ∃ h : H, inducesBlockPermutation (h : Equiv.Perm Ω) σ}

/-- Equality of the already aligned quotient subgroups. -/
def alignedBlockQuotients
    (P Q : Subgroup (Equiv.Perm Ω)) : Prop :=
  blockQuotientSet P = blockQuotientSet Q

/-- A complement after both diagonal components have been removed. -/
def pureBlockC7Complement
    (P W : Subgroup (Equiv.Perm Ω)) : Prop :=
  P ≤ W ∧
    Nonempty (P ≃* C7) ∧
      ∀ p : P, ∃ σ : Equiv.Perm (Fin 7),
        (p : Equiv.Perm Ω) = blockPermutation σ

/-- The complement relation used for the quotient-aligned pair. -/
def complementInside
    (P K Y : Subgroup (Equiv.Perm Ω)) : Prop :=
  P ≤ Y ∧ K ≤ Y ∧ P ⊔ K = Y ∧ P ⊓ K = ⊥

/-- Claim 41242: once Record 16 has removed both diagonal components,
identical quotient subgroups force the two C7 complements to be identical. -/
def claim41242 : Prop :=
  ∀ (W Y K P Q : Subgroup (Equiv.Perm Ω)),
    fullImprimitiveWreath W →
    complementInside P K Y →
    complementInside Q K Y →
    pureBlockC7Complement P W →
    pureBlockC7Complement Q W →
    alignedBlockQuotients P Q →
    P = Q

end MathlibPlus.Open.GroupTheory.R1349Claims41238_41242
