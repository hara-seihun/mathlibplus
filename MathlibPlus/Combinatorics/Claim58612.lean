-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics.Claim58612

/-!
Claim 58612 reports a finite dimension/rank histogram over 62 inverse-pair
directions.  Since the packet gives no direction names, `Fin 62` is used with
an arbitrary ordering that realizes the stated multiplicities.  The identity-
free and inverse-closed atom predicates remain source-specific and are not
silently replaced by properties of this index type.
-/

/-- The reported dimension histogram, with the 62 directions in arbitrary order. -/
def directionDimension (i : Fin 62) : ℕ :=
  if i.1 < 2 then 1 else if i.1 < 22 then 2 else 3

/-- The reported source-atom rank histogram, independently indexed in the same order. -/
def directionRank (i : Fin 62) : ℕ :=
  if i.1 < 2 then 2 else if i.1 < 22 then 3 else 4

/-- Both histograms have multiplicities `2, 20, 40`. -/
theorem dimensionRankProfile :
    (Finset.univ.filter (fun i : Fin 62 => directionDimension i = 1)).card = 2 ∧
      (Finset.univ.filter (fun i : Fin 62 => directionDimension i = 2)).card = 20 ∧
      (Finset.univ.filter (fun i : Fin 62 => directionDimension i = 3)).card = 40 ∧
      (Finset.univ.filter (fun i : Fin 62 => directionRank i = 2)).card = 2 ∧
      (Finset.univ.filter (fun i : Fin 62 => directionRank i = 3)).card = 20 ∧
      (Finset.univ.filter (fun i : Fin 62 => directionRank i = 4)).card = 40 := by
  native_decide

end MathlibPlus.Combinatorics.Claim58612
