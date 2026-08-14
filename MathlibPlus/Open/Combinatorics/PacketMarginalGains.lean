import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Combinatorics.PacketMarginalGains

/-- The three tagged gain grids: one block of size `M` and two distinct copies
of a block of size `N`.  The tags make the multiplicity of the second grid
explicit rather than identifying equal numerical gains. -/
abbrev PacketIndex (M N : ℕ) := Fin M ⊕ (Fin N ⊕ Fin N)

/-- The degree contribution of selecting `j` modes from a block of size `m`. -/
def packetF (m j : ℕ) : ℤ :=
  (j : ℤ) * ((m : ℤ) - (j : ℤ))

/-- The marginal gain from increasing a block selection from `j` to `j+1`. -/
def packetGain (m j : ℕ) : ℤ :=
  (m : ℤ) - 1 - 2 * (j : ℤ)

/-- The gain attached to one of the three tagged blocks. -/
def packetGainAt (M N : ℕ) : PacketIndex M N → ℤ
  | Sum.inl j => packetGain M j
  | Sum.inr (Sum.inl j) => packetGain N j
  | Sum.inr (Sum.inr j) => packetGain N j

/-- The prefix selection corresponding to the allocation `(a,u,v)`. -/
noncomputable def packetPrefix (M N a u v : ℕ) : Finset (PacketIndex M N) := by
  classical
  exact Finset.univ.filter fun i =>
    match i with
    | Sum.inl j => j.val < a
    | Sum.inr (Sum.inl j) => j.val < u
    | Sum.inr (Sum.inr j) => j.val < v

/-- Feasible allocations of a fixed total packet size. -/
def packetFeasible (M N k a u v : ℕ) : Prop :=
  a ≤ M ∧ u ≤ N ∧ v ≤ N ∧ a + u + v = k

/-- The degree of a packet with block allocations `(a,u,v)`. -/
def packetDegree (M N a u v : ℕ) : ℤ :=
  packetF M a + packetF N u + packetF N v

/-- The sum of the marginal gains selected by an allocation. -/
def packetGainSum (M N a u v : ℕ) : ℤ :=
  (∑ j ∈ Finset.range a, packetGain M j) +
    (∑ j ∈ Finset.range u, packetGain N j) +
    (∑ j ∈ Finset.range v, packetGain N j)

/-- A prefix allocation selects the largest available gains, with ties allowed.
The two copies of the `N` grid remain distinct through `PacketIndex`. -/
def packetSelectsLargestGains (M N a u v : ℕ) : Prop :=
  ∀ ⦃i : PacketIndex M N⦄, i ∈ packetPrefix M N a u v →
    ∀ ⦃j : PacketIndex M N⦄, j ∉ packetPrefix M N a u v →
      packetGainAt M N j ≤ packetGainAt M N i

/-- Claim 2891.  For `f_m(j)=j(m-j)`, the marginal gains are
`m-1-2j`; the degree at fixed packet size is therefore maximized exactly by
selecting the largest gains, with multiplicity, from one `M` grid and two `N`
grids.  All carriers used here are the three finite grids displayed in the
claim; the declaration is intentionally proof-free. -/
def claim2891_marginalGainCharacterization : Prop :=
  (∀ (m j : ℕ),
    packetF m (j + 1) - packetF m j = packetGain m j) ∧
  (∀ (M N a u v : ℕ),
    packetDegree M N a u v = packetGainSum M N a u v) ∧
  (∀ (M N k a u v : ℕ),
    packetFeasible M N k a u v →
      ((∀ (a' u' v' : ℕ),
          packetFeasible M N k a' u' v' →
            packetDegree M N a' u' v' ≤ packetDegree M N a u v) ↔
        packetSelectsLargestGains M N a u v))

end MathlibPlus.Open.Combinatorics.PacketMarginalGains
