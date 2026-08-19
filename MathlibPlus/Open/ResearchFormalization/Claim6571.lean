import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Claim6571

noncomputable section

abbrev F5 := ZMod 5
abbrev U := Fin 3 → F5
abbrev V := U × U

/-- The cubic map in the exact rank-six coupled Hénon carrier. -/
def henonF (z : U) : U :=
  ![z 0 ^ 2 + z 0 * z 1 * z 2, z 1 ^ 2, z 2 ^ 2]

/-- The coupled Hénon permutation used by the packet. -/
def q (p : V) : V :=
  (p.2, p.1 + henonF p.2)

/-- The signed mixed differences defining `W_z`. -/
def signedMixedDefects (z : U) : Set U :=
  {w | ∃ a : U,
    w = henonF (a + z) - henonF a - henonF z ∨
    w = henonF (a - z) - henonF a - henonF (-z)}

/-- The exact `𝔽₅`-span of the mixed differences. -/
def mixedDefectSpan (z : U) : Submodule F5 U :=
  Submodule.span F5 (signedMixedDefects z)

/-- The fibre `W_z × {z}` in `U_x ⊕ U_z`. -/
def mixedDifferenceFibre (z : U) : Set V :=
  {p | p.2 = z ∧ p.1 ∈ mixedDefectSpan z}

def e₁ : U := ![1, 0, 0]
def e₂ : U := ![0, 1, 0]
def e₃ : U := ![0, 0, 1]
def e₂₃ : U := e₂ + e₃

/-- The four source directions. -/
def sourceDirections : Set U :=
  {e₁, e₂, e₃, e₂₃}

/-- The signed direction set `D ∪ (-D)`. -/
def signedSourceDirections : Set U :=
  sourceDirections ∪ Set.image (fun z : U => -z) sourceDirections

/-- The exact inverse-closed connection set. -/
def connectionSet : Set V :=
  ⋃ z ∈ signedSourceDirections, mixedDifferenceFibre z

/-- The additive Cayley relation used for the graph interface. -/
def cayleyRelation (S : Set V) (u v : V) : Prop :=
  v - u ∈ S

/-- A graph isomorphism stated directly on the Cayley relations. -/
def cayleyGraphIsomorphism (S T : Set V) (f : V → V) : Prop :=
  Function.Bijective f ∧
    ∀ u v : V,
      cayleyRelation S u v ↔ cayleyRelation T (f u) (f v)

/-- Claim 6571: the exact mixed-difference connection set is transported by
`q`, and `q` is the resulting Cayley-graph isomorphism. -/
def cayleyRelation_transport_claim6571 : Prop :=
  (∀ u v : V,
      v - u ∈ connectionSet ↔
        q v - q u ∈ q '' connectionSet) ∧
    cayleyGraphIsomorphism connectionSet (q '' connectionSet) q

end

end MathlibPlus.Open.ResearchFormalization.Claim6571
