-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is a root of the Unverified library rather than of MathlibPlus and no build here depends on it. See unverified.txt.
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace MathlibPlus.Combinatorics.Claim44831

/-!
# The `b = 2` balanced-tribes calculation

The eight Boolean variables are encoded by the binary digits of `Fin 256`.
The four width-two tribes are the four adjacent pairs of digits.  The signed
encoding of the Boolean target is used for the posterior means; with this
encoding the one-coordinate posterior-variance drop is the squared difference
of the two conditional means divided by four.
-/

private abbrev Assignment := Fin 256

private def bit (x : Assignment) (j : Fin 8) : Bool := Nat.testBit x.val j.val

private def tribes (x : Assignment) : Bool :=
  (bit x 0 && bit x 1) || (bit x 2 && bit x 3) ||
    (bit x 4 && bit x 5) || (bit x 6 && bit x 7)

private def flip (i : Fin 8) (x : Assignment) : Assignment :=
  Fin.ofNat 256 (x.val ^^^ (2 ^ i.val))

/-- Uniform pivot probability for the balanced-tribes target. -/
private def influence (i : Fin 8) : ℚ :=
  ((Finset.univ.filter (fun x : Assignment => tribes x != tribes (flip i x))).card : ℚ) /
    (Fintype.card Assignment)

private def signedTarget (x : Assignment) : ℚ := if tribes x then 1 else -1

private def posteriorMean (i : Fin 8) (b : Bool) : ℚ :=
  (Finset.sum (Finset.univ.filter (fun x : Assignment => bit x i = b)) signedTarget) /
    ((Finset.univ.filter (fun x : Assignment => bit x i = b)).card : ℚ)

/-- The actual one-step posterior-variance drop in the signed normalization. -/
private def oneStepVarianceDrop (i : Fin 8) : ℚ :=
  (posteriorMean i true - posteriorMean i false) ^ 2 / 4

/-- Claim 44831: every displayed variable has influence `27/128` and actual
one-step variance drop `729/16384`. -/
theorem balancedTribes_b2_claim44831 :
    ∀ i : Fin 8,
      influence i = 27 / 128 ∧
        oneStepVarianceDrop i = 729 / 16384 := by
  native_decide

end MathlibPlus.Combinatorics.Claim44831
