import Mathlib
import MathlibPlus.Algebra.Claim41959

namespace MathlibPlus.Open.FormalizationBatch.R1202SixBlock

noncomputable section

private abbrev Plane (p : ℕ) := MathlibPlus.Algebra.Claim41959.V p
private abbrev SixLabels := Equiv.Perm (Fin 3)
private abbrev Point (p : ℕ) := Plane p × SixLabels

private def productAction {p : ℕ}
    (a : Equiv.Perm (Plane p)) (b : Equiv.Perm SixLabels) :
    Equiv.Perm (Point p) :=
  Equiv.prodCongr a b

private def firstAction {p : ℕ}
    (a : Equiv.Perm (Plane p)) : Equiv.Perm (Point p) :=
  productAction a (1 : Equiv.Perm SixLabels)

private def secondAction {p : ℕ}
    (b : Equiv.Perm SixLabels) : Equiv.Perm (Point p) :=
  productAction (1 : Equiv.Perm (Plane p)) b

private def leftRegularSubgroup : Subgroup (Equiv.Perm SixLabels) :=
  Subgroup.closure (Set.range (fun s : SixLabels => Equiv.mulLeft s))

private def directProductCopy {p : ℕ} [NeZero p]
    (K : Subgroup (Equiv.Perm (Plane p))) :
    Subgroup (Equiv.Perm (Point p)) :=
  Subgroup.closure
    (Set.range (fun a : K => firstAction a.1) ∪
      Set.range (fun s : SixLabels => secondAction (Equiv.mulLeft s)))

private def directProductKernel {p : ℕ} [NeZero p]
    (K : Subgroup (Equiv.Perm (Plane p))) :
    Subgroup (Equiv.Perm (Point p)) :=
  Subgroup.closure (Set.range (fun a : K => firstAction a.1))

private def block {p : ℕ} [NeZero p]
    (s : SixLabels) : Finset (Point p) :=
  (Finset.univ : Finset (Plane p)).image (fun v => (v, s))

private def blocks (p : ℕ) [NeZero p] : Finset (Finset (Point p)) :=
  (Finset.univ : Finset SixLabels).image block

private def regularAction {α : Type*} [Fintype α]
    (H : Subgroup (Equiv.Perm α)) : Prop :=
  ∀ x y : α, ∃! h : H, (h : Equiv.Perm α) x = y

private def sixBlockSystem (p : ℕ) [NeZero p] : Prop :=
  let bs := blocks p
  (bs.card = 6) ∧
    (∀ B ∈ bs, B.card = p ^ 2) ∧
    (∀ B ∈ bs, ∀ C ∈ bs, B = C ∨ Disjoint B C) ∧
    bs.biUnion id = Finset.univ

private def preservesBlocks {p : ℕ} [NeZero p]
    (H : Subgroup (Equiv.Perm (Point p))) : Prop :=
  ∀ h : H, ∀ B ∈ blocks p,
    ∃ C ∈ blocks p,
      (h : Equiv.Perm (Point p)) '' (B : Set (Point p)) = (C : Set (Point p))

private def realizesQuotient {p : ℕ} [NeZero p]
    (h : Equiv.Perm (Point p)) (q : Equiv.Perm SixLabels) : Prop :=
  ∀ v : Plane p, ∀ s : SixLabels, (h (v, s)).2 = q s

private def quotientImage {p : ℕ} [NeZero p]
    (H : Subgroup (Equiv.Perm (Point p))) : Set (Equiv.Perm SixLabels) :=
  {q | ∃ h : H, realizesQuotient h.1 q}

private def characteristicSubgroup
    {α : Type*} [Fintype α]
    (H K : Subgroup (Equiv.Perm α)) : Prop :=
  K ≤ H ∧
    ∀ φ : H ≃* H, ∀ x : H,
      (x : Equiv.Perm α) ∈ K → (φ x : Equiv.Perm α) ∈ K

private def directProductAbstract {p : ℕ} [NeZero p]
    (K : Subgroup (Equiv.Perm (Plane p)))
    (H : Subgroup (Equiv.Perm (Point p))) : Prop :=
  Nonempty (H ≃* (K × SixLabels))

private def directProductCp2S3 {p : ℕ} [NeZero p]
    (H : Subgroup (Equiv.Perm (Point p))) : Prop :=
  Nonempty (H ≃* (Multiplicative (Plane p) × SixLabels))

private def kernelIsCyclicPrime {p : ℕ} [NeZero p]
    (K : Subgroup (Equiv.Perm (Point p))) : Prop :=
  Nonempty (K ≃* Multiplicative (ZMod p))

/-- Claim 32191: the two explicit rank-two affine groups are lifted with
one common left-regular action of `S₃` on six labels.  The displayed carrier
has the common six blocks, equal literal quotient action, distinct
characteristic `p`-kernels, and their common `C_p` intersection. -/
def directProductSixBlockObstruction_claim32191 : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p), Odd p →
    letI : NeZero p := ⟨hp.ne_zero⟩
    let P := MathlibPlus.Algebra.Claim41959.P p
    let Q := MathlibPlus.Algebra.Claim41959.Q p
    let Pcopy := directProductCopy P
    let Qcopy := directProductCopy Q
    let Pkernel := directProductKernel P
    let Qkernel := directProductKernel Q
    sixBlockSystem p ∧
      Nat.card (Point p) = 6 * p ^ 2 ∧
      regularAction Pcopy ∧
      regularAction Qcopy ∧
      directProductAbstract P Pcopy ∧
      directProductAbstract Q Qcopy ∧
      directProductCp2S3 Pcopy ∧
      directProductCp2S3 Qcopy ∧
      Nat.card Pcopy = 6 * p ^ 2 ∧
      Nat.card Qcopy = 6 * p ^ 2 ∧
      preservesBlocks Pcopy ∧
      preservesBlocks Qcopy ∧
      quotientImage Pcopy = (leftRegularSubgroup : Set (Equiv.Perm SixLabels)) ∧
      quotientImage Qcopy = (leftRegularSubgroup : Set (Equiv.Perm SixLabels)) ∧
      characteristicSubgroup Pcopy Pkernel ∧
      characteristicSubgroup Qcopy Qkernel ∧
      Pkernel ≠ Qkernel ∧
      Nat.card Pkernel = p ^ 2 ∧
      Nat.card Qkernel = p ^ 2 ∧
      Nat.card
          ((Pkernel ⊓ Qkernel) : Subgroup (Equiv.Perm (Point p))) = p ∧
      kernelIsCyclicPrime
        ((Pkernel ⊓ Qkernel) : Subgroup (Equiv.Perm (Point p)))

end

end MathlibPlus.Open.FormalizationBatch.R1202SixBlock
