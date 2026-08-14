import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

abbrev Nonagon := ZMod 9

/-- The polygon-edge capacity in the all-unique-four incidence fixture. -/
def nonagonKappa (x y : Nonagon) : ℕ :=
  if x = y then 0
  else if y = x + 1 ∨ y = x - 1 then 1
  else 2

/-- The four-point class in the circulant fixture, indexed by its centre. -/
def circulantClass (c : Nonagon) : Finset Nonagon :=
  {c + 1, c + 2, c + 4, c + 6}

/-- Its incidence matrix, with rows indexed by centres and columns by points. -/
def circulantIncidence (c x : Nonagon) : ℕ :=
  if x ∈ circulantClass c then 1 else 0

def pointPairMultiplicity (x y : Nonagon) : ℕ :=
  ∑ c : Nonagon, circulantIncidence c x * circulantIncidence c y

def centrePairMultiplicity (c d : Nonagon) : ℕ :=
  ∑ x : Nonagon, circulantIncidence c x * circulantIncidence d x

def pointDeficit (x y : Nonagon) : ℕ :=
  nonagonKappa x y - pointPairMultiplicity x y

def centreDeficit (c d : Nonagon) : ℕ :=
  nonagonKappa c d - centrePairMultiplicity c d

/-- The three disjoint triangles on the residue classes modulo three. -/
def triangleDeficit (x y : Nonagon) : ℕ :=
  if y = x + 3 ∨ y = x - 3 then 1 else 0

/--
The exact finite incidence content of R-3744.6.  The final two conjuncts spell
out the two pair-capacity constraints, while `triangleDeficit` records that both
weighted deficit matrices are the three triangles `{0,3,6}`, `{1,4,7}`, and
`{2,5,8}`.
-/
def r3744_6_circulant_fixture : Prop :=
  (∀ c : Nonagon, circulantIncidence c c = 0) ∧
  (∀ c : Nonagon, ∑ x : Nonagon, circulantIncidence c x = 4) ∧
  (∀ x : Nonagon, ∑ c : Nonagon, circulantIncidence c x = 4) ∧
  (∀ x y : Nonagon, x ≠ y → pointPairMultiplicity x y ≤ nonagonKappa x y) ∧
  (∀ c d : Nonagon, c ≠ d → centrePairMultiplicity c d ≤ nonagonKappa c d) ∧
  (∀ x y : Nonagon, pointDeficit x y = triangleDeficit x y) ∧
  (∀ c d : Nonagon, centreDeficit c d = triangleDeficit c d)

end MathlibPlus.Open.ResearchFormalization
