import Mathlib
import MathlibPlus.Open.LinearAlgebra.DeletionStableBoundedAnchor
import MathlibPlus.Open.MatroidBatch

namespace MathlibPlus.Open.ResearchFormalization.R1255Repair

noncomputable section

abbrev QuotientCoordinate (q : ℕ) := ZMod q
abbrev LayerCoordinate := ZMod 3
abbrev Point (N : Type*) (q : ℕ) :=
  (QuotientCoordinate q × N) × LayerCoordinate

def thetaPower {N : Type*} [AddCommGroup N]
    (θ : N ≃+ N) (i : LayerCoordinate) : N ≃+ N :=
  match i.val with
  | 0 => AddEquiv.refl N
  | 1 => θ
  | _ => θ.trans θ

def localOrderThreeFixedPointFree {N : Type*} [AddCommGroup N]
    (θ : N ≃+ N) : Prop :=
  θ ≠ AddEquiv.refl N ∧
    (∀ x : N, θ (θ (θ x)) = x) ∧
      (∀ x : N, θ x = x → x = 0)

def quotientScalarOrderThree (q : ℕ) (ω : ZMod q) : Prop :=
  ω ^ 3 = 1 ∧ ω ≠ 1 ∧
    ∀ y : ZMod q, ω * y = y → y = 0

def rightTranslationFormula {N : Type*} [AddCommGroup N]
    {q : ℕ} (ω : ZMod q) (θ : N ≃+ N)
    (x : N) (z : ZMod q) (j : LayerCoordinate)
    (p : Equiv.Perm (Point N q)) : Prop :=
  ∀ b n i,
    p ((b, n), i) =
      (((ω ^ j.val)⁻¹ * (b + z), n + thetaPower θ i x), i + j)

def exactRightRegularCopy {N : Type*} [AddCommGroup N]
    {q : ℕ} (ω : ZMod q) (θ : N ≃+ N)
    (R : Subgroup (Equiv.Perm (Point N q))) : Prop :=
  ∀ p : Equiv.Perm (Point N q),
    p ∈ R ↔
      ∃ (x : N) (z : ZMod q) (j : LayerCoordinate),
        rightTranslationFormula ω θ x z j p

def globalLayer {N : Type*} {q : ℕ}
    (i : LayerCoordinate) : Set (Point N q) :=
  {p | p.2 = i}

def globalLayerPartition {N : Type*} {q : ℕ} : Set (Set (Point N q)) :=
  {globalLayer (N := N) (q := q) 0,
    globalLayer (N := N) (q := q) 1,
    globalLayer (N := N) (q := q) 2}

def derivedKernel {Ω : Type*}
    (R : Subgroup (Equiv.Perm Ω)) : Subgroup (Equiv.Perm Ω) :=
  Subgroup.map R.subtype (commutator R)

def subgroupOrbit {Ω : Type*}
    (K : Subgroup (Equiv.Perm Ω)) (x : Ω) : Set Ω :=
  {y | ∃ k : K, (k : Equiv.Perm Ω) x = y}

def characteristicPartition {Ω : Type*}
    (R : Subgroup (Equiv.Perm Ω)) : Set (Set Ω) :=
  Set.range (subgroupOrbit (derivedKernel R))

def block {N : Type*} {q : ℕ} (b : ZMod q) : Set (Point N q) :=
  {p | p.1.1 = b}

def preservesBlockSystem {N : Type*} {q : ℕ}
    (R : Subgroup (Equiv.Perm (Point N q))) : Prop :=
  ∀ r ∈ R, ∀ b : ZMod q, ∃ c : ZMod q,
    Set.image r (block (N := N) (q := q) b) = block c

def inducedBlockAction {N : Type*} {q : ℕ}
    (R : Subgroup (Equiv.Perm (Point N q))) : Set (Equiv.Perm (ZMod q)) :=
  {σ | ∃ r ∈ R, ∀ p : Point N q,
    σ p.1.1 = (r p).1.1}

def scalarQuotientAction (q : ℕ) (ω : ZMod q) :
    Set (Equiv.Perm (ZMod q)) :=
  {σ | ∃ z : ZMod q, ∃ j : LayerCoordinate, ∀ b,
    σ b = (ω ^ j.val)⁻¹ * (b + z)}

def orientationMapFun {N : Type*} {q : ℕ}
    (ε : QuotientCoordinate q → Bool) : Point N q → Point N q :=
  fun p => (p.1, if ε p.1.1 then -p.2 else p.2)

/-- A permutation witness is required to be exactly the source's pointwise
orientation map; no unconstrained permutation callback is admitted. -/
def orientationWitness {N : Type*} {q : ℕ}
    (ε : QuotientCoordinate q → Bool)
    (F : Equiv.Perm (Point N q)) : Prop :=
  ∀ p : Point N q, F p = orientationMapFun ε p

def conjugatedCopy {Ω : Type*}
    (F : Equiv.Perm Ω) (R : Subgroup (Equiv.Perm Ω)) :
    Subgroup (Equiv.Perm Ω) :=
  Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj F)) R

def constantCode {q : ℕ} (ε : QuotientCoordinate q → Bool) : Prop :=
  (∀ b, ε b = false) ∨ (∀ b, ε b = true)

def partitionContext {N : Type*} [AddCommGroup N] [Fintype N]
    (q : ℕ) (ω : ZMod q) (θ : N ≃+ N)
    (R : Subgroup (Equiv.Perm (Point N q))) : Prop :=
  Nat.Prime q ∧ q % 3 = 1 ∧
    quotientScalarOrderThree q ω ∧
      localOrderThreeFixedPointFree θ ∧
        exactRightRegularCopy ω θ R ∧
          characteristicPartition R = globalLayerPartition

def alignedBlockAndLocalData {N : Type*} {q : ℕ}
    (ω : ZMod q) (R T : Subgroup (Equiv.Perm (Point N q)))
    (ε : QuotientCoordinate q → Bool) : Prop :=
  preservesBlockSystem R ∧ preservesBlockSystem T ∧
    inducedBlockAction R = scalarQuotientAction q ω ∧
      inducedBlockAction T = scalarQuotientAction q ω ∧
        ∀ b : ZMod q, ∀ p : Point N q,
          p ∈ block b →
            (p.2 = 0 → orientationMapFun ε p = p) ∧
              ((ε b = false → orientationMapFun ε p = p) ∧
                (ε b = true →
                  orientationMapFun ε p = (p.1, -p.2)))

/-- Claim 30661: a nonconstant exact orientation witness supplies two copies
with the same block/quotient/local data and different characteristic
partitions. -/
def claim30661 : Prop :=
  ∀ {N : Type*} [AddCommGroup N] [Fintype N]
    (q : ℕ) (ω : ZMod q) (θ : N ≃+ N)
    (R : Subgroup (Equiv.Perm (Point N q))),
    partitionContext q ω θ R →
      ∀ ε : QuotientCoordinate q → Bool, ¬ constantCode ε →
        ∃ F : Equiv.Perm (Point N q),
          orientationWitness ε F ∧
            let T := conjugatedCopy F R
            alignedBlockAndLocalData ω R T ε ∧
              characteristicPartition T ≠ characteristicPartition R

def exactControl {N : Type*} [AddCommGroup N] [Fintype N]
    (q : ℕ) [NeZero q]
    (degree codeCount constantCount breakerCount : ℕ) : Prop :=
  ∃ (ω : ZMod q) (θ : N ≃+ N)
    (R : Subgroup (Equiv.Perm (Point N q))),
    partitionContext q ω θ R ∧
      Nat.card (Point N q) = degree ∧
        Fintype.card (QuotientCoordinate q → Bool) = codeCount ∧
          Set.ncard {ε : QuotientCoordinate q → Bool | constantCode ε} =
            constantCount ∧
            Set.ncard {ε : QuotientCoordinate q → Bool | ¬ constantCode ε} =
              breakerCount ∧
              (∀ ε : QuotientCoordinate q → Bool,
                ∃ F : Equiv.Perm (Point N q),
                  orientationWitness ε F ∧
                    (characteristicPartition
                        (conjugatedCopy F R) = characteristicPartition R ↔
                      constantCode ε))

/-- Claim 30662: the four exact controls retain their degrees, normalized-code
counts, constant/breaker counts, and characteristic-partition test. -/
def claim30662 : Prop :=
  exactControl (N := ZMod 7) 7 147 128 2 126 ∧
    exactControl (N := ZMod 7 × ZMod 7) 7 1029 128 2 126 ∧
      exactControl (N := ZMod 13) 7 273 128 2 126 ∧
        exactControl (N := ZMod 7) 13 273 8192 2 8190

end
end MathlibPlus.Open.ResearchFormalization.R1255Repair
