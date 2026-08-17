import Mathlib

namespace MathlibPlus.Open.Research.R1330Formalization_41040

noncomputable section

abbrev V (p : ℕ) := ZMod p × ZMod p
abbrev S3 := Equiv.Perm (Fin 3)
abbrev Ω (p : ℕ) := V p × S3

/-- The binomial quadratic used by the two coordinate shears. -/
def binomTwo (p : ℕ) (t : ZMod p) : ZMod p :=
  (Nat.choose t.val 2 : ZMod p)

def shearA (p : ℕ) : V p → V p :=
  fun z => (z.1, z.2 + binomTwo p z.1)

def shearB (p : ℕ) : V p → V p :=
  fun z => (z.1 + binomTwo p z.2, z.2)

/-- The three labels in A₃ are the rotation blocks. -/
def rotationLabel (s : S3) : Prop :=
  s.sign = (1 : ℤˣ)

def rotationLabels : Set S3 :=
  {s | rotationLabel s}

def blockShear (p : ℕ) : Ω p → Ω p :=
  fun z =>
    @ite (Ω p) (rotationLabel z.2)
      (Classical.propDecidable (rotationLabel z.2))
      (shearA p z.1, z.2)
      (shearB p z.1, z.2)

/-- The natural left-regular permutation of V × S₃. -/
def regularGenerator (p : ℕ) (g : Ω p) : Equiv.Perm (Ω p) :=
  Equiv.prodCongr (Equiv.addLeft g.1) (Equiv.mulLeft g.2)

def regularCopy (p : ℕ) : Subgroup (Equiv.Perm (Ω p)) :=
  Subgroup.closure (Set.range (regularGenerator p))

def conjugationHom {G : Type*} [Group G] (g : G) : G →* G :=
  (MulAut.conj g : G ≃* G).toMonoidHom

def conjugateSubgroup {G : Type*} [Group G]
    (g : G) (H : Subgroup G) : Subgroup G :=
  H.map (conjugationHom g)

def generatedGroup (p : ℕ) (F : Equiv.Perm (Ω p)) :
    Subgroup (Equiv.Perm (Ω p)) :=
  Subgroup.closure
    ((regularCopy p : Set (Equiv.Perm (Ω p))) ∪
      (conjugateSubgroup F (regularCopy p) : Set (Equiv.Perm (Ω p))))

def translationKernel (p : ℕ) : Subgroup (Equiv.Perm (Ω p)) :=
  Subgroup.closure
    (Set.range (fun v : V p => regularGenerator p (v, 1)))

def translatedKernel (p : ℕ) (F : Equiv.Perm (Ω p)) :
    Subgroup (Equiv.Perm (Ω p)) :=
  conjugateSubgroup F (translationKernel p)

def fixesBlocks {p : ℕ} (k : Equiv.Perm (Ω p)) : Prop :=
  ∀ z : Ω p, (k z).2 = z.2

def blockKernel (p : ℕ) (F k : Equiv.Perm (Ω p)) : Prop :=
  k ∈ generatedGroup p F ∧ fixesBlocks k

def actsAsPair (p : ℕ) (a b : Equiv.Perm (V p))
    (k : Equiv.Perm (Ω p)) : Prop :=
  (∀ z : Ω p, z.2 ∈ rotationLabels →
    k z = (a z.1, z.2)) ∧
  (∀ z : Ω p, z.2 ∉ rotationLabels →
    k z = (b z.1, z.2))

def fullProductKernel (p : ℕ) [NeZero p] (F : Equiv.Perm (Ω p)) : Prop :=
  (∀ k : Equiv.Perm (Ω p), blockKernel p F k →
    ∃ a b : Equiv.Perm (V p),
      a ∈ alternatingGroup (V p) ∧
      b ∈ alternatingGroup (V p) ∧
      actsAsPair p a b k) ∧
  (∀ a b : Equiv.Perm (V p),
    a ∈ alternatingGroup (V p) →
    b ∈ alternatingGroup (V p) →
    ∃ k : Equiv.Perm (Ω p), blockKernel p F k ∧ actsAsPair p a b k)

def graphKernelCase (p : ℕ) [NeZero p] (F : Equiv.Perm (Ω p)) : Prop :=
  ∃ φ : alternatingGroup (V p) ≃* alternatingGroup (V p),
    ∀ k : Equiv.Perm (Ω p),
      blockKernel p F k ↔
        ∃ a : alternatingGroup (V p),
          actsAsPair p (a : Equiv.Perm (V p))
            (φ a : Equiv.Perm (V p)) k

def realizes (f : Equiv.Perm α) (g : α → α) : Prop :=
  ∀ x, f x = g x

def isCharacteristicIn {G : Type*} [Group G]
    (R N : Subgroup G) : Prop :=
  N ≤ R ∧
    ∀ φ : R ≃* R, ∀ x : R,
      (x : G) ∈ N → (φ x : G) ∈ N

def characteristicTranslationKernel (p : ℕ) [NeZero p] : Prop :=
  isCharacteristicIn (regularCopy p) (translationKernel p) ∧
    Nonempty (translationKernel p ≃* Multiplicative (V p)) ∧
    Nat.card (translationKernel p) = p ^ 2

def characteristicTranslatedKernel (p : ℕ) [NeZero p] (F : Equiv.Perm (Ω p)) : Prop :=
  isCharacteristicIn (conjugateSubgroup F (regularCopy p))
      (translatedKernel p F) ∧
    Nonempty (translatedKernel p F ≃* Multiplicative (V p)) ∧
    Nat.card (translatedKernel p F) = p ^ 2

def orderPSubgroup {G : Type*} [Group G]
    (p : ℕ) (N D : Subgroup G) : Prop :=
  D ≤ N ∧ Nat.card D = p

def conjugatesTo {G : Type*} [Group G]
    (m : G) (E D : Subgroup G) : Prop :=
  conjugateSubgroup m E = D

def allPrimeLineConjugacy (p : ℕ) [NeZero p] (F : Equiv.Perm (Ω p)) : Prop :=
  ∀ D E : Subgroup (Equiv.Perm (Ω p)),
    orderPSubgroup p (translationKernel p) D →
    orderPSubgroup p (translatedKernel p F) E →
    ∃ m : generatedGroup p F,
      conjugatesTo (m : Equiv.Perm (Ω p)) E D

def fullCopiesConjugate (p : ℕ) (F : Equiv.Perm (Ω p)) : Prop :=
  ∃ m : generatedGroup p F,
    conjugateSubgroup (m : Equiv.Perm (Ω p)) (regularCopy p) =
      conjugateSubgroup F (regularCopy p)

/-- Claim 41040. -/
def claim41040 : Prop :=
  ∀ p : ℕ, ∀ hp : Nat.Prime p, Odd p →
    letI : NeZero p := ⟨hp.ne_zero⟩
    ∃ F : Equiv.Perm (Ω p),
      (∀ z : Ω p, F z = blockShear p z) ∧
      blockKernel p F F ∧
      characteristicTranslationKernel p ∧
      characteristicTranslatedKernel p F ∧
      allPrimeLineConjugacy p F


end

end MathlibPlus.Open.Research.R1330Formalization_41040
