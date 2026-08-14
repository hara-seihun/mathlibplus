import Mathlib

namespace MathlibPlus.Open.AdmittedBatch.R45702

/-- The finite family in the six-member bit-mask model. -/
def sourceFamily : Finset ℕ :=
  {50, 63, 194, 207, 242, 255}

/-- Bit-mask union is the set union operation used by the finite model. -/
def maskUnion (a b : ℕ) : ℕ := a ||| b

/-- Adjoining the displayed root to a source is its root-closure operation. -/
def rootClosure (root source : ℕ) : ℕ := maskUnion source root

/-- A finite family of bit masks is union-closed. -/
def IsUnionClosed (family : Finset ℕ) : Prop :=
  ∀ ⦃a b : ℕ⦄, a ∈ family → b ∈ family → maskUnion a b ∈ family

/-- The sources moved by the root closure, restricted to the displayed family. -/
def nonfixedSources (root : ℕ) : Finset ℕ :=
  sourceFamily.filter (fun source => rootClosure root source ≠ source)

/--
The locally sharp one-root example from the admitted claim: adding the root
preserves union-closedness, and precisely the three displayed sources are
nonfixed under root closure.
-/
def localSharpnessOneRoot : Prop :=
  IsUnionClosed (insert 13 sourceFamily) ∧
    nonfixedSources 13 = {50, 194, 242}

end MathlibPlus.Open.AdmittedBatch.R45702
