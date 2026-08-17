import MathlibPlus.Open.ResearchFormalization.R4220Claim53348

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R4220.Claim53347

open MathlibPlus.Open.ResearchFormalization.R4220.Claim53348

noncomputable section

abbrev Vertex53347 := Vertex53348 6
abbrev EdgeSet53347 := EdgeSet53348 6

def path6Edges53347 : EdgeSet53347 :=
  {(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)}

def sourceVertexLabel53347 (i : Vertex53347) : ℕ :=
  i.val + 1

def centralEdge53347 : EdgeSet53347 :=
  {(1, 2)}

def centralSet53347 : Finset Vertex53347 :=
  {1, 2}

def sourceCentralSet53347 : Finset ℕ :=
  {2, 3}

def sourceImage53347 (C : Finset Vertex53347) : Finset ℕ :=
  C.image sourceVertexLabel53347

def centralCard53347 : MvPolynomial ℕ ℤ :=
  cardPolynomial53348 path6Edges53347 centralSet53347

def x1_53347 : MvPolynomial ℕ ℤ :=
  MvPolynomial.X 1

def x2_53347 : MvPolynomial ℕ ℤ :=
  MvPolynomial.X 2

def centralFormula53347 : MvPolynomial ℕ ℤ :=
  (x2_53347 + x1_53347 ^ 2) ^ 2

/-- Every component represented in every forest term of the deleted card has
order strictly below the threshold. -/
def allCardComponentsBelowThreshold53347
    (E : EdgeSet53347) (V : Finset Vertex53347) (h : ℕ) : Prop :=
  ∀ A ∈ (E.filter (fun e => e.1 ∈ V ∧ e.2 ∈ V)).powerset,
    ∀ u ∈ representatives53348 A V,
      componentSize53348 A V u < h

def centralCardAllComponentsBelow53347 : Prop :=
  allCardComponentsBelowThreshold53347
    (deleteCardEdges53348 path6Edges53347 centralSet53347)
    (Finset.univ \ centralSet53347) 3

/-- Claim 53347: the source-labelled central edge is `{2,3}`, its deletion
uses the corresponding zero-based set `{1,2}`, and the resulting card is the
stated P2-disjoint-union polynomial with all component orders below three. -/
def claim_53347 : Prop :=
  path6Edges53347 =
      {(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)} ∧
    centralEdge53347 = {(1, 2)} ∧
    centralEdge53347 ⊆ path6Edges53347 ∧
    sourceImage53347 centralSet53347 = sourceCentralSet53347 ∧
    centralCard53347 = centralFormula53347 ∧
    centralCardAllComponentsBelow53347

end

end MathlibPlus.Open.ResearchFormalization.R4220.Claim53347
