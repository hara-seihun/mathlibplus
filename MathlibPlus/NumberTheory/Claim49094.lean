-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import MathlibPlus.Basic

namespace MathlibPlus.NumberTheory

/-- The exact finite counterexample to replacing a minimizing binomial index by
an arbitrary divisor representative. -/
theorem divisorRepresentativeShortcut_counterexample :
    (Nat.factorization (Nat.choose 210 30)) 2 = 4 ∧
      (Nat.factorization (Nat.choose 210 30)) 3 = 0 ∧
      (Nat.factorization (Nat.choose 210 30)) 5 = 0 ∧
      (Nat.factorization (Nat.choose 210 30)) 7 = 2 ∧
      Nat.gcd 210 (Nat.choose 210 30) = 14 ∧
      210 / Nat.gcd 210 (Nat.choose 210 30) = 15 ∧
      15 ∣ 210 ∧
      (Nat.factorization (Nat.choose 210 15)) 2 = 4 ∧
      (Nat.factorization (Nat.choose 210 15)) 3 = 1 ∧
      (Nat.factorization (Nat.choose 210 15)) 5 = 1 ∧
      (Nat.factorization (Nat.choose 210 15)) 7 = 2 ∧
      Nat.gcd 210 (Nat.choose 210 15) = 210 ∧
      210 / Nat.gcd 210 (Nat.choose 210 15) = 1 := by
  native_decide

/-- The packet's printed `v₅ = 9` for `choose 210 15` is not the exact
valuation; the preceding theorem records the verified value `1`. -/
theorem divisorRepresentativeShortcut_reported_v5_is_false :
    (Nat.factorization (Nat.choose 210 15)) 5 ≠ 9 := by
  native_decide

end MathlibPlus.NumberTheory
