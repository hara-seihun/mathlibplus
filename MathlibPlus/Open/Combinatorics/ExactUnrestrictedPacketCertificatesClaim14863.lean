import Mathlib

namespace MathlibPlus.Open.Combinatorics.ExactUnrestrictedPacketCertificatesClaim14863

noncomputable section

open Classical
open scoped BigOperators

/-- A Catalan word in dimension `d` has `d+1` up-steps and `d+1`
 down-steps.  `true` denotes `U` and `false` denotes `D`. -/
abbrev RawWord (d : ℕ) := Fin (2 * (d + 1)) → Bool

private def upCount {d : ℕ} (w : RawWord d)
    (t : Fin (2 * (d + 1) + 1)) : ℕ :=
  ((Finset.univ : Finset (Fin (2 * (d + 1)))).filter
    (fun i => i.val < t.val ∧ w i = true)).card

private def downCount {d : ℕ} (w : RawWord d)
    (t : Fin (2 * (d + 1) + 1)) : ℕ :=
  ((Finset.univ : Finset (Fin (2 * (d + 1)))).filter
    (fun i => i.val < t.val ∧ w i = false)).card

private def isDyck {d : ℕ} (w : RawWord d) : Prop :=
  upCount w ⟨2 * (d + 1), by omega⟩ = d + 1 ∧
    ∀ t, downCount w t ≤ upCount w t

private def upBefore {d : ℕ} (w : RawWord d)
    (i : Fin (2 * (d + 1))) : Finset (Fin (2 * (d + 1))) :=
  (Finset.univ : Finset (Fin (2 * (d + 1)))).filter
    (fun j => j.val < i.val ∧ w j = true)

private def downBefore {d : ℕ} (w : RawWord d)
    (i : Fin (2 * (d + 1))) : Finset (Fin (2 * (d + 1))) :=
  (Finset.univ : Finset (Fin (2 * (d + 1)))).filter
    (fun j => j.val < i.val ∧ w j = false)

/-- The Young-lattice row lengths read from a Dyck word. -/
private def shapePart {d : ℕ} (w : RawWord d) (r : Fin (d + 1)) : ℕ :=
  let target := d + 1 - r.val - 1
  ((Finset.univ : Finset (Fin (2 * (d + 1)))).filter
    (fun i => w i = true ∧ (upBefore w i).card = target)).sum
    (fun i => (downBefore w i).card)

private def shapeArea {d : ℕ} (w : RawWord d) : ℕ :=
  ∑ r : Fin (d + 1), shapePart w r

private def wordLE {d : ℕ} (u v : RawWord d) : Prop :=
  ∀ r : Fin (d + 1), shapePart u r ≤ shapePart v r

/-- The cells of the Young-lattice skew shape `σ/ρ`. -/
private def skewCells {d : ℕ} (rho sigma : RawWord d) :
    Finset (Fin (d + 1) × Fin (d + 1)) :=
  (Finset.univ : Finset (Fin (d + 1) × Fin (d + 1))).filter (fun c =>
    shapePart rho c.1 ≤ c.2.val ∧ c.2.val < shapePart sigma c.1)

/-- A rook strip has at most one skew cell in each row and at most one in each
column; distinct skew cells are therefore allowed. -/
private def isRookStrip {d : ℕ} (rho sigma : RawWord d) : Prop :=
  (∀ r : Fin (d + 1),
    ((skewCells rho sigma).filter (fun c => c.1 = r)).card ≤ 1) ∧
    (∀ c : Fin (d + 1),
      ((skewCells rho sigma).filter (fun p => p.2 = c)).card ≤ 1)

/-- An even-bottom Boolean Young-lattice packet. -/
private def isEvenBottomBooleanPacket {d : ℕ}
    (rho sigma : RawWord d) : Prop :=
  isDyck rho ∧ isDyck sigma ∧ wordLE rho sigma ∧
    Even (shapeArea rho) ∧ isRookStrip rho sigma

private def intervalMember {d : ℕ}
    (rho sigma mu : RawWord d) : Prop :=
  wordLE rho mu ∧ wordLE mu sigma

/-- The attachment sequence used by the DTS perfect-matching model. -/
private abbrev Attachment (d : ℕ) :=
  Fin (d + 1) → Fin (2 * (d + 1) + 1)

private def validAttachment {d : ℕ} (p : Attachment d) : Prop :=
  ∀ i, (p i).val ≤ 2 * i.val

private def attachmentList {d : ℕ} (p : Attachment d) : List ℕ :=
  List.ofFn (fun i : Fin (d + 1) => (p i).val)

private def insertUD (w : List Bool) (p : ℕ) : List Bool :=
  w.take p ++ [true, false] ++ w.drop p

private def insertUThenD (w : List Bool) (p : ℕ) : List Bool :=
  w.take p ++ [true] ++ w.drop p ++ [false]

private def dtsWord {d : ℕ} (p : Attachment d) : List Bool :=
  (attachmentList p).foldl (fun w i => insertUD w i) []

private def matchingWord {d : ℕ} (p : Attachment d) : List Bool :=
  (attachmentList p).foldl (fun w i => insertUThenD w i) []

/-- The inverse-cup coefficient `c_(λ,μ)`, represented by the exact DTS
attachment carrier from the admitted perfect-matching insertion model. -/
private def inverseCupCoefficient (d : ℕ)
    (lambda mu : RawWord d) : ℕ :=
  Fintype.card
    {p : Attachment d //
      validAttachment p ∧
        dtsWord p = List.ofFn lambda ∧
        matchingWord p = List.ofFn mu}

private def packetContains {d : ℕ}
    (rho sigma mu : RawWord d) : Prop :=
  isEvenBottomBooleanPacket rho sigma ∧ intervalMember rho sigma mu

private def packetRank {d : ℕ}
    (rho sigma : RawWord d) : ℕ :=
  shapeArea sigma - shapeArea rho

/-- An exact nonnegative-integer decomposition of one inverse-cup row into
Boolean packets. -/
private def hasPacketDecomposition (d : ℕ) (lambda : RawWord d)
    (a : RawWord d → RawWord d → ℕ) : Prop :=
  isDyck lambda ∧
    (∀ rho sigma,
      ¬ isEvenBottomBooleanPacket rho sigma → a rho sigma = 0) ∧
    (∀ mu, isDyck mu →
      inverseCupCoefficient d lambda mu =
        ∑ rho : RawWord d, ∑ sigma : RawWord d,
          if packetContains rho sigma mu then a rho sigma else 0)

/-- The number of packet occurrences of a specified rank in a family of row
certificates.  Coefficients count repeated packet occurrences. -/
private def packetRankCount (d : ℕ)
    (certificates : RawWord d → RawWord d → RawWord d → ℕ) (q : ℕ) : ℕ :=
  ∑ lambda : RawWord d, ∑ rho : RawWord d, ∑ sigma : RawWord d,
    if isDyck lambda ∧ isEvenBottomBooleanPacket rho sigma ∧
        packetRank rho sigma = q then
      certificates lambda rho sigma
    else 0

/-- The alternating `UD` Catalan word representing the maximal staircase row
in dimension six. -/
def maximalStaircaseWord : RawWord 6 :=
  ![true, false, true, false, true, false, true, false,
    true, false, true, false, true, false]

/-- The reported dimension-five rank histogram. -/
def dimensionFivePacketRankHistogram : Fin 6 → ℕ :=
  ![320, 783, 508, 153, 22, 1]

/-- Claim 14863: every inverse-cup row through dimension five has an exact
unrestricted even-bottom Boolean-packet decomposition; the dimension-five
rank histogram is attached to one such family of decompositions; and the two
specified dimension-six test rows, one explicitly the maximal staircase row,
have exact decompositions, with the latter using rank five. -/
def exactUnrestrictedPacketCertificates_claim14863 : Prop :=
  (Fintype.card {w : RawWord 1 // isDyck w} = 2 ∧
    Fintype.card {w : RawWord 2 // isDyck w} = 5 ∧
    Fintype.card {w : RawWord 3 // isDyck w} = 14 ∧
    Fintype.card {w : RawWord 4 // isDyck w} = 42 ∧
    Fintype.card {w : RawWord 5 // isDyck w} = 132) ∧
  (∀ d : ℕ, 1 ≤ d → d ≤ 5 →
    ∀ lambda : RawWord d, isDyck lambda →
      ∃ a : RawWord d → RawWord d → ℕ,
        hasPacketDecomposition d lambda a) ∧
  (∃ certificates : RawWord 5 → RawWord 5 → RawWord 5 → ℕ,
    (∀ lambda : RawWord 5, isDyck lambda →
      hasPacketDecomposition 5 lambda (certificates lambda)) ∧
    (∀ lambda rho sigma, isDyck lambda →
      certificates lambda rho sigma ≠ 0 → packetRank rho sigma ≤ 5) ∧
    (∀ q : Fin 6,
      packetRankCount 5 certificates q =
        dimensionFivePacketRankHistogram q)) ∧
  (∃ other : RawWord 6,
    other ≠ maximalStaircaseWord ∧ isDyck other ∧
      ∃ a : RawWord 6 → RawWord 6 → ℕ,
        hasPacketDecomposition 6 other a) ∧
  (∃ a : RawWord 6 → RawWord 6 → ℕ,
    isDyck maximalStaircaseWord ∧
      hasPacketDecomposition 6 maximalStaircaseWord a ∧
      (∀ rho sigma, a rho sigma ≠ 0 → packetRank rho sigma ≤ 5) ∧
      (∃ rho sigma, a rho sigma ≠ 0 ∧ packetRank rho sigma = 5))

end
end MathlibPlus.Open.Combinatorics.ExactUnrestrictedPacketCertificatesClaim14863
