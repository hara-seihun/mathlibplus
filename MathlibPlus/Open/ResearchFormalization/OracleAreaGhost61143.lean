import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.OracleAreaGhost61143

noncomputable section

open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

/-- The two values of a uniform Rademacher sign. -/
def signValue (s : Bool) : ℝ := if s then 1 else -1

/-- A length-`d` address and its indexed leaf-sign table. -/
abbrev Address (d : ℕ) := Fin d → Bool
abbrev Leaves (d : ℕ) := Address d → Bool
abbrev GhostAddresses (d r : ℕ) := Fin r → Address d
abbrev GhostState (d r : ℕ) := Address d × Leaves d × GhostAddresses d r

/-- The finite uniform expectation used for the product law of addresses,
leaves, and the first `r` independent ghost addresses. -/
def uniformAverage {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (Fintype.card α : ℝ)⁻¹ * ∑ x, f x

/-- The address-tree target `Y_A`. -/
def target (d r : ℕ) (s : GhostState d r) : ℝ :=
  signValue (s.2.1 s.1)

/-- The transcript after `r` complete ghost blocks.  The actual address is
present exactly after the first block, and each ghost leaf answer is cached. -/
abbrev GhostTranscript (d r : ℕ) :=
  (GhostAddresses d r) × (Option (Address d) × (Fin r → Bool))

def ghostTranscript (d r : ℕ) (s : GhostState d r) : GhostTranscript d r :=
  (s.2.2,
    (if 0 < r then some s.1 else none,
      fun j => s.2.1 (s.2.2 j)))

def sameGhostTranscript (d r : ℕ) (t : GhostTranscript d r)
    (s : GhostState d r) : Prop :=
  ghostTranscript d r s = t

noncomputable def ghostFiber (d r : ℕ) (t : GhostTranscript d r) :
    Finset (GhostState d r) :=
  letI : DecidablePred (sameGhostTranscript d r t) :=
    fun s => Classical.propDecidable _
  Finset.univ.filter (sameGhostTranscript d r t)

def finiteConditionalVariance {α : Type*} [Fintype α]
    (f : α → ℝ) (cell : Finset α) : ℝ :=
  if cell.Nonempty then
    let q : ℝ := cell.card
    (∑ x ∈ cell, (f x) ^ 2) / q - ((∑ x ∈ cell, f x) / q) ^ 2
  else 0

def ghostPosteriorVariance (d r : ℕ) (t : GhostTranscript d r) : ℝ :=
  finiteConditionalVariance (target d r) (ghostFiber d r t)

def expectedGhostVariance (d r : ℕ) : ℝ :=
  uniformAverage (fun s : GhostState d r =>
    ghostPosteriorVariance d r (ghostTranscript d r s))

def ghostBlockEndpointArea (d : ℕ) : ℝ :=
  ∑' r : ℕ, expectedGhostVariance d r

/-- The transcript of the answer-aligned policy after `m` actual queries.
The first `d` queries reveal the address in coordinate order and the next
query reveals the selected leaf; after that terminal transcript is held fixed. -/
abbrev AlignedState (d : ℕ) := Address d × Leaves d
abbrev AlignedTranscript (d : ℕ) :=
  (Fin d → Option Bool) × Option Bool

def alignedTranscript (d m : ℕ) (s : AlignedState d) : AlignedTranscript d :=
  (fun i => if i.1 < min m d then some (s.1 i) else none,
    if d < m then some (s.2 s.1) else none)

def sameAlignedTranscript (d m : ℕ) (t : AlignedTranscript d)
    (s : AlignedState d) : Prop :=
  alignedTranscript d m s = t

noncomputable def alignedFiber (d m : ℕ) (t : AlignedTranscript d) :
    Finset (AlignedState d) :=
  letI : DecidablePred (sameAlignedTranscript d m t) :=
    fun s => Classical.propDecidable _
  Finset.univ.filter (sameAlignedTranscript d m t)

def alignedTarget (d : ℕ) (s : AlignedState d) : ℝ :=
  signValue (s.2 s.1)

def alignedPosteriorVariance (d m : ℕ) (t : AlignedTranscript d) : ℝ :=
  finiteConditionalVariance (alignedTarget d) (alignedFiber d m t)

def expectedAlignedVariance (d m : ℕ) : ℝ :=
  uniformAverage (fun s : AlignedState d =>
    alignedPosteriorVariance d m (alignedTranscript d m s))

def alignedQueryByQueryArea (d : ℕ) : ℝ :=
  ∑' m : ℕ, expectedAlignedVariance d m

/-- Claim 61143: the independent-ghost block-endpoint geometric law and the
exact root-inclusive area, together with the linear answer-aligned policy. -/
def claim_61143 : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    let d := k - 1
    let N : ℝ := (2 : ℝ) ^ d
    (∀ r : ℕ,
      expectedGhostVariance d r = (1 - N⁻¹) ^ r) ∧
      ghostBlockEndpointArea d = N ∧
      alignedQueryByQueryArea d = (k : ℝ)

end

end MathlibPlus.Open.ResearchFormalization.OracleAreaGhost61143
