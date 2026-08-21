-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import Mathlib

namespace MathlibPlus.Combinatorics

open scoped BigOperators

/--
Exact arithmetic certificate for the seven subgroup orders displayed in
Claim 37835.  The subgroup and coset-system constructions remain source
carriers; this receipt retains their literal order list, its cardinality and
sum, divisibility by the order 72 ambient group, and the 46-minus-7 residual.
-/
theorem claim37835_subgroupOrderCertificate :
    let orders : Finset ℕ := {3, 4, 8, 9, 12, 24, 36}
    orders.card = 7 ∧
      orders.sum id = 96 ∧
      (∀ n ∈ orders, n ∣ 72) ∧
      46 - orders.card = 39 := by
  native_decide

end MathlibPlus.Combinatorics
