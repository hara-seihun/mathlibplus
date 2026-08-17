import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1179.Claim31909

noncomputable section

abbrev C3Squared := Multiplicative (Fin 2 → ZMod 3)
abbrev D10 := DihedralGroup 5
abbrev G := C3Squared × D10

/-- The exact inverse-closed connection-set carrier on `C₃² × D₁₀`. -/
def isConnectionSet (S : Set G) : Prop :=
  (1 : G) ∉ S ∧
    ∀ g : G, g ∈ S ↔ g⁻¹ ∈ S

/-- The left-step relation used by the labelled thick/thin fibre model. -/
def leftStep (S : Set G) (x y : G) : Prop :=
  ∃ g ∈ S, g * x = y

/-- The Cayley graph with the source's left multiplication convention. -/
def cayleyGraph (S : Set G) : SimpleGraph G :=
  SimpleGraph.fromRel (leftStep S)

def graphIsomorphism (S T : Set G) : Prop :=
  Nonempty ((cayleyGraph S).Iso (cayleyGraph T))

def graphAutomorphism (Γ : SimpleGraph G) (e : Equiv.Perm G) : Prop :=
  ∀ x y, Γ.Adj x y ↔ Γ.Adj (e x) (e y)

def fullGraphAutomorphismSubgroup (Γ : SimpleGraph G)
    (Aut : Subgroup (Equiv.Perm G)) : Prop :=
  ∀ e : Equiv.Perm G, e ∈ Aut ↔ graphAutomorphism Γ e

/-- The exact five-square census filter, including a genuine Sylow-5 object. -/
def fiveSquareRow (S : Set G) : Prop :=
  isConnectionSet S ∧
    Set.ncard S = 10 ∧
    SimpleGraph.Connected (cayleyGraph S) ∧
    ∃ Aut : Subgroup (Equiv.Perm G),
      fullGraphAutomorphismSubgroup (cayleyGraph S) Aut ∧
        ∃ P : Sylow 5 Aut, 25 ≤ Nat.card P

/-- The natural derived `C₅` block through a vertex. -/
def naturalC5Orbit (x : G) : Set G :=
  {y | ∃ k : ZMod 5,
    y = x * ((1 : C3Squared), DihedralGroup.r k)}

def preservesNaturalC5Partition (S : Set G) : Prop :=
  ∀ e : Equiv.Perm G,
    graphAutomorphism (cayleyGraph S) e →
      ∀ x y : G,
        y ∈ naturalC5Orbit x ↔
          e y ∈ naturalC5Orbit (e x)

/-- The five symmetric fibre factors in the intrinsic action. -/
abbrev IntrinsicBase := ZMod 5 → Equiv.Perm C3Squared

/-- The displayed dihedral action on the five matching coordinates. -/
def dihedralIndexAction (g : D10) (i : ZMod 5) : ZMod 5 :=
  g.casesOn (fun a => i + a) (fun a => -a - i)

/-- The displayed coordinate action on the symmetric base. -/
def coordinateActionLaw
    (θ : D10 →* MulAut IntrinsicBase) : Prop :=
  ∀ g : D10, ∀ f : IntrinsicBase, ∀ i : ZMod 5,
    (θ g) f i = f (dihedralIndexAction (g⁻¹) i)

abbrev IntrinsicGroup
    (θ : D10 →* MulAut IntrinsicBase) :=
  SemidirectProduct IntrinsicBase D10 θ

def intrinsicFibreKernel
    (θ : D10 →* MulAut IntrinsicBase) :
    Subgroup (IntrinsicGroup θ) :=
  (SemidirectProduct.rightHom : IntrinsicGroup θ →* D10).ker

/-- The actual ten graph fibres, with the two labelled sides retained. -/
def fibrePoint (i : ZMod 5) (side : Bool) : D10 :=
  if side then DihedralGroup.r i * DihedralGroup.sr 0 else DihedralGroup.r i

def intrinsicFiber (i : ZMod 5) (side : Bool) : Set G :=
  {x | ∃ a : C3Squared, x = (a, fibrePoint i side)}

/-- Full intrinsic ten-fibre action data.  The quotient action is tied to the
actual graph fibres, rather than being a regular action on an abstract copy of
`D₁₀`. -/
def intrinsicTenFibreData (S : Set G)
    (θ : D10 →* MulAut IntrinsicBase)
    (q : D10 →* Equiv.Perm (ZMod 5 × Bool))
    (φ : IntrinsicGroup θ →* Equiv.Perm G) : Prop :=
  coordinateActionLaw θ ∧
    (∀ h : IntrinsicGroup θ,
      graphAutomorphism (cayleyGraph S) (φ h)) ∧
    (∀ e : Equiv.Perm G,
      graphAutomorphism (cayleyGraph S) e ↔
        ∃! h : IntrinsicGroup θ, φ h = e) ∧
    Nat.card (intrinsicFibreKernel θ) = (Nat.factorial 9) ^ 5 ∧
    (∀ g : D10, ∀ i : ZMod 5, ∀ side : Bool,
      φ (SemidirectProduct.inr (φ := θ) g) '' intrinsicFiber i side =
        intrinsicFiber ((q g) (i, side)).1 ((q g) (i, side)).2) ∧
    (∀ u v : ZMod 5 × Bool, ∃! g : D10, (q g) u = v) ∧
    (∀ i : ZMod 5, ∀ σ : Equiv.Perm C3Squared, ∀ side : Bool,
      ∃ b : IntrinsicBase,
        b i = σ ∧
          ∀ a : C3Squared,
            φ (SemidirectProduct.inl (φ := θ) b)
                (a, fibrePoint i side) =
              (σ a, fibrePoint i side))

/-- The displayed thick/thin connection set. -/
def thickThinConnection : Set G :=
  ((Set.univ : Set C3Squared) ×ˢ
      ({DihedralGroup.sr 0} : Set D10)) ∪
    {((1 : C3Squared), DihedralGroup.r 1 * DihedralGroup.sr 0)}

/-- Claim 31909: the five exact Sylow-filtered rows have one unique
partition-breaking representative, whose labelled thick/thin graph carries
the full `S₉⁵ ⋊ D₁₀` intrinsic ten-fibre action. -/
def claim31909 : Prop :=
  ∃ rows : Fin 5 → Set G,
    (∀ i : Fin 5, fiveSquareRow (rows i)) ∧
    (∀ i j : Fin 5,
      graphIsomorphism (rows i) (rows j) → i = j) ∧
    (∀ S : Set G, fiveSquareRow S →
      ∃ i : Fin 5, graphIsomorphism S (rows i)) ∧
    ∃ i : Fin 5,
      rows i = thickThinConnection ∧
      ¬ preservesNaturalC5Partition (rows i) ∧
      (∃ θ : D10 →* MulAut IntrinsicBase,
        ∃ q : D10 →* Equiv.Perm (ZMod 5 × Bool),
          ∃ φ : IntrinsicGroup θ →* Equiv.Perm G,
            intrinsicTenFibreData (rows i) θ q φ) ∧
      (∀ j : Fin 5,
        ¬ preservesNaturalC5Partition (rows j) ↔ j = i)

end

end MathlibPlus.Open.ResearchFormalization.R1179.Claim31909
