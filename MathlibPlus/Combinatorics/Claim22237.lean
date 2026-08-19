import MathlibPlus.Open.Combinatorics.BalancedBlockClaims

namespace MathlibPlus.Combinatorics.Claim22237

open MathlibPlus.Open.Combinatorics.BalancedBlockClaims

/--
Endpoint switching adds the coboundary `t_i+t_j` to every balanced-block sign.
It preserves each cyclic triangle sum and transports both homogeneous
transversal predicates, so their existence and nonexistence are unchanged.
-/
def triangle_sum_switch_invariant_claim22237 : Prop :=
  ∀ (n : Nat) (s : Fin n → Fin n → ZMod 2) (t : Fin n → ZMod 2),
    let switched : Fin n → Fin n → ZMod 2 :=
      fun i j => s i j + t i + t j
    (∀ i j k : Fin n,
      switched i j + switched j k + switched k i =
        s i j + s j k + s k i) ∧
    ∀ k : Nat,
      (CliqueTransversal (k := k) s ↔
        CliqueTransversal (k := k) switched) ∧
      (IndependentTransversal (k := k) s ↔
        IndependentTransversal (k := k) switched)

end MathlibPlus.Combinatorics.Claim22237
