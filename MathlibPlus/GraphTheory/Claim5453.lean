-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is a root of the Unverified library rather than of MathlibPlus and no build here depends on it. See unverified.txt.
import MathlibPlus.Basic

namespace MathlibPlus.GraphTheory.Claim5453

/-- The distance-one-from-an-endpoint indicator on the seven-vertex path is the
second-jet combination `1 + choose(degree, 2) - m`. -/
theorem nearEndpoint_indicator_identity_claim5453 :
    let V := Fin 7
    let adjacent : V → V → Bool := fun v w =>
      decide (v.1 + 1 = w.1 ∨ w.1 + 1 = v.1)
    let degree : V → ℕ := fun v =>
      (Finset.univ.filter (fun w => adjacent v w)).card
    let m : V → ℕ := fun v =>
      ∑ w ∈ Finset.univ.filter (fun w => adjacent v w), (degree w - 1)
    ∀ v : V,
      (if v = 1 ∨ v = 5 then (1 : ℤ) else 0) =
        1 + (Nat.choose (degree v) 2 : ℤ) - (m v : ℤ) := by
  native_decide

end MathlibPlus.GraphTheory.Claim5453
