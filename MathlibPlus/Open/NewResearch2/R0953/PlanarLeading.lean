import Mathlib

namespace MathlibPlus.Open.NewResearch2.R0953

noncomputable section

/-- The planar free magma basis with generators `a` and `b`. -/
inductive PlanarTree where
  | a
  | b
  | node (left right : PlanarTree)
deriving DecidableEq

namespace PlanarTree

/-- Vertex weight: a newly formed binary branch contributes the extra one. -/
def weight : PlanarTree → ℕ
  | .a => 1
  | .b => 2
  | .node x y => 1 + weight x + weight y

/-- Prefix words with the symbol order `node > b > a`, encoded by
`node = 2`, `b = 1`, and `a = 0`. -/
def prefixWord : PlanarTree → List ℕ
  | .a => [0]
  | .b => [1]
  | .node x y => 2 :: (prefixWord x ++ prefixWord y)

/-- The first-leaf replacement for the corridor derivation rule.  The
coefficient two in the `b` rule is irrelevant to the leading basis term but is
retained in `deriv` below. -/
def firstRewrite : PlanarTree → PlanarTree
  | .a => .b
  | .b => .node .a .a
  | .node x y => .node (firstRewrite x) y

/-- Multiplication of finitely supported planar basis combinations. -/
noncomputable def treeMul (f g : PlanarTree →₀ ℚ) : PlanarTree →₀ ℚ :=
  f.sum fun x cx =>
    g.sum fun y cy => Finsupp.single (.node x y) (cx * cy)

/-- The derivation with `∂a=b`, `∂b=2(a a)`, extended by the Leibniz rule. -/
noncomputable def deriv : PlanarTree → PlanarTree →₀ ℚ
  | .a => Finsupp.single .b 1
  | .b => Finsupp.single (.node .a .a) 2
  | .node x y =>
      treeMul (deriv x) (Finsupp.single y 1) +
        treeMul (Finsupp.single x 1) (deriv y)

/-- The vertex-weight grading stated for the planar free magma. -/
def claim27538_vertexWeightGrading : Prop :=
  weight .a = 1 ∧
    weight .b = 2 ∧
    ∀ x y, weight (.node x y) = 1 + weight x + weight y

/-- Prefix order and the exact first-leaf leading-term assertion. -/
def claim27541_planarPrefixFirstLeafLeadingTerm : Prop :=
  ∀ t,
    firstRewrite t ∈ (deriv t).support ∧
      ∀ r ∈ (deriv t).support,
        r = firstRewrite t ∨
          List.Lex (fun u v : ℕ => u < v)
            (prefixWord r) (prefixWord (firstRewrite t))

/-- The first-leaf leading rewrite is injective on planar magma basis trees. -/
def claim27542_firstLeafLeadingRewriteInjective : Prop :=
  Function.Injective firstRewrite

end PlanarTree

end

end MathlibPlus.Open.NewResearch2.R0953
