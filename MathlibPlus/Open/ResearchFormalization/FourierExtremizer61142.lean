import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.FourierExtremizer61142

noncomputable section

open scoped BigOperators

/-- A finite Rademacher cube on a finite coordinate set. -/
abbrev Cube (S : Finset ℕ) := {i : ℕ // i ∈ S} → Bool

/-- The real sign represented by a Boolean cube coordinate. -/
def signValue (b : Bool) : ℝ :=
  if b then 1 else -1

/-- Uniform averaging on a finite Rademacher cube. -/
def cubeAverage (S : Finset ℕ) (f : Cube S → ℝ) : ℝ :=
  (∑ x : Cube S, f x) / (Fintype.card (Cube S) : ℝ)

/-- Finite deterministic coordinate decision trees with sign-valued leaves. -/
inductive SignTree where
  | leaf (value : Bool)
  | query (coordinate : ℕ) (ifNegative ifPositive : SignTree)

namespace SignTree

/-- The maximum number of coordinate queries on a path. -/
def depth : SignTree → ℕ
  | .leaf _ => 0
  | .query _ ifNegative ifPositive =>
      1 + max (depth ifNegative) (depth ifPositive)

/-- Evaluation of a tree on a Boolean coordinate oracle. -/
def evaluate : SignTree → (ℕ → Bool) → Bool
  | .leaf value, _ => value
  | .query coordinate ifNegative ifPositive, oracle =>
      if oracle coordinate then evaluate ifPositive oracle
      else evaluate ifNegative oracle

/-- The finite set of coordinates appearing in a tree. -/
def support : SignTree → Finset ℕ
  | .leaf _ => ∅
  | .query coordinate ifNegative ifPositive =>
      insert coordinate (support ifNegative ∪ support ifPositive)

/-- Relabel every coordinate of a tree. -/
def mapCoordinates (map : ℕ → ℕ) : SignTree → SignTree
  | .leaf value => .leaf value
  | .query coordinate ifNegative ifPositive =>
      .query (map coordinate)
        (mapCoordinates map ifNegative) (mapCoordinates map ifPositive)

/-- The coordinates revealed along the input-dependent evaluation path. -/
def queryTrace : SignTree → (ℕ → Bool) → List ℕ
  | .leaf _, _ => []
  | .query coordinate ifNegative ifPositive, oracle =>
      coordinate ::
        if oracle coordinate then queryTrace ifPositive oracle
        else queryTrace ifNegative oracle

end SignTree

/-- Extend a cube assignment by the fixed value `false` off its coordinate set. -/
def extendCube (S : Finset ℕ) (x : Cube S) : ℕ → Bool :=
  fun i => if h : i ∈ S then x ⟨i, h⟩ else false

/-- The real-valued function computed by a sign tree on a finite cube. -/
def treeValue (S : Finset ℕ) (T : SignTree) (x : Cube S) : ℝ :=
  signValue (T.evaluate (extendCube S x))

/-- A Walsh character indexed by a coordinate subset. -/
def walshCharacter (S A : Finset ℕ) (x : Cube S) : ℝ :=
  Finset.prod A (fun i => if h : i ∈ S then signValue (x ⟨i, h⟩) else 1)

/-- The Walsh coefficient of a finite-cube function. -/
noncomputable def walshCoefficient (S : Finset ℕ) (f : Cube S → ℝ)
    (A : Finset ℕ) : ℝ :=
  cubeAverage S (fun x => f x * walshCharacter S A x)

/-- The Walsh spectral `l^1` norm, including the constant coefficient. -/
noncomputable def walshSpectralL1 (S : Finset ℕ) (f : Cube S → ℝ) : ℝ :=
  Finset.sum S.powerset (fun A => |walshCoefficient S f A|)

/-- The nonzero Walsh support of a finite-cube function. -/
def walshSupport (S : Finset ℕ) (f : Cube S → ℝ) : Set (Finset ℕ) :=
  {A | A ∈ S.powerset ∧ walshCoefficient S f A ≠ 0}

/-- The mean of a tree output on a finite coordinate cube. -/
def treeMean (S : Finset ℕ) (T : SignTree) : ℝ :=
  cubeAverage S (treeValue S T)

/-- Sign-valuedness of the real function computed by a tree. -/
def treeIsSignValued (S : Finset ℕ) (T : SignTree) : Prop :=
  ∀ x : Cube S, treeValue S T x = 1 ∨ treeValue S T x = -1

/-- The Walsh norm of a tree viewed on a specified finite coordinate set. -/
def treeWalshSpectralL1 (S : Finset ℕ) (T : SignTree) : ℝ :=
  walshSpectralL1 S (treeValue S T)

/-- Multiplication by the Walsh character of one root coordinate. -/
def rootModulate (S : Finset ℕ) (root : ℕ) (f : Cube S → ℝ)
    (x : Cube S) : ℝ :=
  signValue (extendCube S x root) * f x

/-- The four Walsh support families in `A`, `B`, `xA`, and `xB` are pairwise disjoint. -/
def fourWalshFamiliesDisjoint (S : Finset ℕ) (root : ℕ)
    (a b : Cube S → ℝ) : Prop :=
  let xa := rootModulate S root a
  let xb := rootModulate S root b
  Disjoint (walshSupport S a) (walshSupport S b) ∧
    Disjoint (walshSupport S a) (walshSupport S xa) ∧
    Disjoint (walshSupport S a) (walshSupport S xb) ∧
    Disjoint (walshSupport S b) (walshSupport S xa) ∧
    Disjoint (walshSupport S b) (walshSupport S xb) ∧
    Disjoint (walshSupport S xa) (walshSupport S xb)

/-- The input-dependent path of coordinate reveals. -/
def pathQueries (S : Finset ℕ) (T : SignTree) (x : Cube S) : List ℕ :=
  T.queryTrace (extendCube S x)

/-- A tree can be evaluated by legal distinct-coordinate path queries in a bounded number of steps. -/
def adaptivePathQueryBound (S : Finset ℕ) (T : SignTree) (bound : ℕ) : Prop :=
  ∀ x : Cube S,
    (pathQueries S T x).Nodup ∧
      (∀ i, i ∈ pathQueries S T x → i ∈ S) ∧
        (pathQueries S T x).length ≤ bound

/-- The number of coordinates in the complete depth-`d` construction. -/
def blockSize (d : ℕ) : ℕ :=
  2 ^ d - 1

def extremizerUniverse (d : ℕ) : Finset ℕ :=
  Finset.range (blockSize d)

/-- The depth-one Rademacher coordinate tree. -/
def rademacherTree (coordinate : ℕ) : SignTree :=
  .query coordinate (.leaf false) (.leaf true)

/-- The recursively constructed extremizing tree family. -/
def extremizerTree : ℕ → SignTree
  | 0 => .leaf false
  | 1 => rademacherTree 0
  | d + 2 =>
      .query 0
        (SignTree.mapCoordinates
          (fun i => i + blockSize (d + 1) + 1)
          (extremizerTree (d + 1)))
        (SignTree.mapCoordinates (fun i => i + 1)
          (extremizerTree (d + 1)))

def extremizerLeft (d : ℕ) : SignTree :=
  SignTree.mapCoordinates (fun i => i + 1) (extremizerTree d)

def extremizerRight (d : ℕ) : SignTree :=
  SignTree.mapCoordinates
    (fun i => i + blockSize d + 1) (extremizerTree d)

def rootValue (S : Finset ℕ) (x : Cube S) : ℝ :=
  signValue (extendCube S x 0)

/-- The general depth bound for the absolute Walsh normalization. -/
def depthWalshBound : Prop :=
  ∀ (d : ℕ), 1 ≤ d →
    ∀ (S : Finset ℕ) (T : SignTree),
      T.support ⊆ S →
        T.depth ≤ d →
          treeWalshSpectralL1 S T ≤ (2 : ℝ) ^ (d - 1)

/-- The exact recursive extremizer and its adaptive path-query realization. -/
def claim61142 : Prop :=
  depthWalshBound ∧
    extremizerTree 1 = rademacherTree 0 ∧
    (∀ (d : ℕ), 1 ≤ d →
      let S := extremizerUniverse d
      SignTree.depth (extremizerTree d) = d ∧
        treeMean S (extremizerTree d) = 0 ∧
        treeIsSignValued S (extremizerTree d) ∧
        treeWalshSpectralL1 S (extremizerTree d) = (2 : ℝ) ^ (d - 1) ∧
        adaptivePathQueryBound S (extremizerTree d) d ∧
        (∀ x : Cube S,
          (pathQueries S (extremizerTree d) x).length = d)) ∧
    (∀ (d : ℕ), 1 ≤ d →
      let S := extremizerUniverse (d + 1)
      let A := extremizerLeft d
      let B := extremizerRight d
      (∀ x : Cube S,
        treeValue S (extremizerTree (d + 1)) x =
            (treeValue S A x + treeValue S B x) / (2 : ℝ) +
              rootValue S x *
                (treeValue S A x - treeValue S B x) / (2 : ℝ)) ∧
        (∀ x : Cube S,
          rootValue S x = 1 →
            treeValue S (extremizerTree (d + 1)) x = treeValue S A x) ∧
        (∀ x : Cube S,
          rootValue S x = -1 →
            treeValue S (extremizerTree (d + 1)) x = treeValue S B x) ∧
        treeMean S A = 0 ∧
        treeMean S B = 0 ∧
        Disjoint A.support B.support ∧
        0 ∉ A.support ∧
        0 ∉ B.support ∧
        fourWalshFamiliesDisjoint S 0 (treeValue S A) (treeValue S B) ∧
        treeWalshSpectralL1 S (extremizerTree (d + 1)) =
          treeWalshSpectralL1 S A + treeWalshSpectralL1 S B ∧
        treeWalshSpectralL1 S A = (2 : ℝ) ^ (d - 1) ∧
        treeWalshSpectralL1 S B = (2 : ℝ) ^ (d - 1) ∧
        treeWalshSpectralL1 S (extremizerTree (d + 1)) = (2 : ℝ) ^ d)

end

end MathlibPlus.Open.ResearchFormalization.FourierExtremizer61142
