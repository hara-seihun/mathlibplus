-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import MathlibPlus.Basic

set_option maxRecDepth 100000

namespace MathlibPlus.Algebra.Claim43227

/-!
Claim 43227, the Morris coefficient-map period rigidity statement.  The
finite-field model is made literal with `ZMod 3`; the displayed five
coordinates are the map in the claim, and the kernel checks the full finite
universal/existential statement rather than a sample of translations.
-/
theorem periodRigidity :
    let F := ZMod 3
    let W := Fin 3 → F
    let V := Fin 5 → F
    let c : W → V := fun x => ![
      x 0 * (x 1) ^ 2,
      x 0 * (x 2) ^ 2,
      (x 1) ^ 2 * x 2,
      x 1 * (x 2) ^ 2,
      x 0 * x 1 * x 2]
    ∀ u : W, (∃ k : V, ∀ w : W, c (w + u) - c w = k) → u = 0 := by
  decide

end MathlibPlus.Algebra.Claim43227

namespace MathlibPlus.Algebra.Claim31351

/-!
Claim 31351, the explicit binary-fibre holonomy counterexample.  The
connection set is represented literally as the singleton `S = {(a,0)}` in
the additive group `H × F`; the switch is the displayed fibre map
`f(x,z)=(x,z+b(x))`.  The theorem retains inverse-closure, the unchanged
identity-fibre value, the exact cocycle difference, and the resulting failure
to preserve the Cayley matching.  No larger graph API is assumed.
-/
theorem binaryFibreHolonomyCounterexample :
    let F := ZMod 2
    let H := Fin 2 → F
    let G := H × F
    let a : H := ![1, 0]
    let b : H → F := fun x => x 0 * x 1
    let s : G := (a, 0)
    let S : Finset G := {s}
    let f : G → G := fun g => (g.1, g.2 + b g.1)
    b a = 0 ∧
      -s ∈ S ∧
      (∀ x : H, b (x + a) + b x = x 1) ∧
      ¬ (∀ g : G, f (g + s) - f g ∈ S) ∧
      f ((![0, 0] : H), 0) = ((![0, 0] : H), 0) ∧
      f ((![0, 1] : H), 0) - f ((![0, 1] : H) + a, 0) ≠ s := by
  native_decide

end MathlibPlus.Algebra.Claim31351
