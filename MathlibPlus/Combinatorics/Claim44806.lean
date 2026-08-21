-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is a root of the Unverified library rather than of MathlibPlus and no build here depends on it. See unverified.txt.
import Mathlib

namespace MathlibPlus.Combinatorics

open DihedralGroup

abbrev Claim44806D10 := DihedralGroup 5

def claim44806IsConnectionSet (S : Finset Claim44806D10) : Prop :=
  (1 : Claim44806D10) ∉ S ∧
    ∀ g : Claim44806D10, g ∈ S ↔ g⁻¹ ∈ S

instance (S : Finset Claim44806D10) :
    DecidablePred (fun g : Claim44806D10 => g ∈ S ↔ g⁻¹ ∈ S) :=
  fun _ => inferInstance

instance (S : Finset Claim44806D10) :
    Decidable (claim44806IsConnectionSet S) := by
  unfold claim44806IsConnectionSet
  infer_instance

def claim44806ValidConnectionSets :
    Finset (Finset Claim44806D10) :=
  (Finset.univ : Finset (Finset Claim44806D10)).filter
    (fun S => decide (claim44806IsConnectionSet S))

/-- In the loop-free convention, inverse-closed connection sets on D10 are
chosen independently on the two nontrivial rotation inverse pairs and the
five self-inverse reflections. -/
theorem inverseClosedConnectionSet_count_claim44806 :
    claim44806ValidConnectionSets.card = 2 ^ 2 * 2 ^ 5 := by
  native_decide

end MathlibPlus.Combinatorics
