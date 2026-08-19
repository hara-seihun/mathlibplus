import MathlibPlus.Open.ResearchFormalization.R1203.Claim41970
import MathlibPlus.Open.ResearchFormalization.R1203.Claim41973

namespace MathlibPlus.Open.ResearchFormalization.R1203

open MathlibPlus.ResearchFormalization.R1203

/-- The scalar-valued global degree-one cocycles. -/
def scalarGlobalCocycleSpace
    {p : ℕ} {A : Type*} [CommGroup A]
    {rho : MathlibPlus.ResearchFormalization.R1203.c3 →* MulAut A} (omega : ZMod p) :
    Set (eGroup A rho → ZMod p) :=
  {f | MathlibPlus.ResearchFormalization.R1203Claim41970.matchingScalarCocycle
      (A := A) (rho := rho) (omega := omega) f}

/-- The vector-valued global degree-one cocycles. -/
def vectorGlobalCocycleSpace
    {p : ℕ} {A : Type*} [CommGroup A]
    {rho : MathlibPlus.ResearchFormalization.R1203.c3 →* MulAut A} {W : Type*} [AddCommGroup W]
    [DistribMulAction (eGroup A rho) W] :
    Set (eGroup A rho → W) :=
  {f | vectorCocycle (p := p) f}

/-- The scalar-valued degree-one cocycles on a subgroup. -/
def scalarSubgroupCocycleSpace
    {p : ℕ} {A : Type*} [CommGroup A]
    {rho : MathlibPlus.ResearchFormalization.R1203.c3 →* MulAut A} (omega : ZMod p)
    (L : Subgroup (eGroup A rho)) : Set (L → ZMod p) :=
  {z |
    MathlibPlus.ResearchFormalization.R1203Claim41970.subgroupCocycle
      (A := A) (rho := rho) (omega := omega) L z}

/-- The vector-valued degree-one cocycles on a subgroup. -/
def vectorSubgroupCocycleSpace
    {p : ℕ} {A : Type*} [CommGroup A]
    {rho : MathlibPlus.ResearchFormalization.R1203.c3 →* MulAut A} {W : Type*} [AddCommGroup W]
    [DistribMulAction (eGroup A rho) W]
    (L : Subgroup (eGroup A rho)) : Set (L → W) :=
  {z | subgroupCocycle (p := p) L z}

/-- Coordinate functions obtained from a choice of linear basis of `W`. -/
def globalCocycleCoordinates
    {p : ℕ} {A : Type*} [CommGroup A]
    {rho : MathlibPlus.ResearchFormalization.R1203.c3 →* MulAut A} {d : ℕ} {W : Type*}
    [AddCommGroup W] [Module (ZMod p) W]
    (e : W ≃ₗ[ZMod p] (Fin d → ZMod p))
    (f : eGroup A rho → W) :
    Fin d → (eGroup A rho → ZMod p) :=
  fun i h => e (f h) i

/-- Coordinate functions for a subgroup-valued cocycle. -/
def subgroupCocycleCoordinates
    {p : ℕ} {A : Type*} [CommGroup A]
    {rho : MathlibPlus.ResearchFormalization.R1203.c3 →* MulAut A} {d : ℕ} {W : Type*}
    [AddCommGroup W] [Module (ZMod p) W]
    (e : W ≃ₗ[ZMod p] (Fin d → ZMod p))
    (L : Subgroup (eGroup A rho)) (z : L → W) :
    Fin d → (L → ZMod p) :=
  fun i h => e (z h) i

/-- The finite direct-sum carrier for scalar global cocycles. -/
def scalarGlobalCoordinateSpace
    {p : ℕ} {A : Type*} [CommGroup A]
    {rho : MathlibPlus.ResearchFormalization.R1203.c3 →* MulAut A} {d : ℕ} (omega : ZMod p) :
    Set (Fin d → (eGroup A rho → ZMod p)) :=
  {g | ∀ i, g i ∈ scalarGlobalCocycleSpace (A := A) (rho := rho) omega}

/-- The finite direct-sum carrier for scalar subgroup cocycles. -/
def scalarSubgroupCoordinateSpace
    {p : ℕ} {A : Type*} [CommGroup A]
    {rho : MathlibPlus.ResearchFormalization.R1203.c3 →* MulAut A} {d : ℕ} (omega : ZMod p)
    (L : Subgroup (eGroup A rho)) :
    Set (Fin d → (L → ZMod p)) :=
  {g | ∀ i, g i ∈ scalarSubgroupCocycleSpace (A := A) (rho := rho) omega L}

/-- Coordinate splitting and the direct-sum restriction square. -/
def coordinateCocycleSplit
    {p : ℕ} {A : Type*} [CommGroup A]
    {rho : MathlibPlus.ResearchFormalization.R1203.c3 →* MulAut A} {d : ℕ} {W : Type*}
    [AddCommGroup W] [Module (ZMod p) W]
    [DistribMulAction (eGroup A rho) W]
    (omega : ZMod p) (L : Subgroup (eGroup A rho))
    (e : W ≃ₗ[ZMod p] (Fin d → ZMod p)) : Prop :=
  Set.BijOn
      (globalCocycleCoordinates (A := A) (rho := rho) e)
      (vectorGlobalCocycleSpace (p := p) (A := A) (rho := rho) (W := W))
      (scalarGlobalCoordinateSpace (A := A) (rho := rho) omega) ∧
    Set.BijOn
      (subgroupCocycleCoordinates (A := A) (rho := rho) e L)
      (vectorSubgroupCocycleSpace (p := p) (A := A) (rho := rho) L (W := W))
      (scalarSubgroupCoordinateSpace (A := A) (rho := rho) omega L) ∧
    Set.MapsTo
      (fun f : eGroup A rho → W => fun x : L => f x)
      (vectorGlobalCocycleSpace (p := p) (A := A) (rho := rho) (W := W))
      (vectorSubgroupCocycleSpace (p := p) (A := A) (rho := rho) L (W := W)) ∧
    Set.MapsTo
      (fun f : eGroup A rho → ZMod p => fun x : L => f x)
      (scalarGlobalCocycleSpace (A := A) (rho := rho) omega)
      (scalarSubgroupCocycleSpace (A := A) (rho := rho) omega L) ∧
    (∀ f : eGroup A rho → W,
      f ∈ vectorGlobalCocycleSpace
        (p := p) (A := A) (rho := rho) (W := W) →
      subgroupCocycleCoordinates (A := A) (rho := rho) e L
        (fun x : L => f x) =
        (fun i => fun x : L =>
          globalCocycleCoordinates (A := A) (rho := rho) e f i x))

/-- Vector-valued matching cocycles split into scalar coordinates, and the
restriction map is the direct sum of the scalar restriction maps for every
choice of basis. -/
def claim41972 : Prop :=
  ∀ (p : ℕ) [Fact (Nat.Prime p)], Nat.ModEq 3 p 1 →
    ∀ (A : Type*) [CommGroup A] [Fintype A]
      (rho : MathlibPlus.ResearchFormalization.R1203.c3 →* MulAut A) (omega : ZMod p)
      (V : Sylow p A),
      matchingScalarAction (rho := rho) p omega V →
      ∀ (d : ℕ) (W : Type*) [AddCommGroup W]
        [Module (ZMod p) W] [FiniteDimensional (ZMod p) W]
        [DistribMulAction (eGroup A rho) W],
        1 ≤ d → Module.finrank (ZMod p) W = d →
        matchingModule (p := p) (omega := omega) (A := A) (rho := rho) W →
        Nonempty (W ≃ₗ[ZMod p] (Fin d → ZMod p)) ∧
          ∀ (L : Subgroup (eGroup A rho))
            (e : W ≃ₗ[ZMod p] (Fin d → ZMod p)),
            coordinateCocycleSplit
              (p := p) (A := A) (rho := rho) (W := W)
              omega L e

end MathlibPlus.Open.ResearchFormalization.R1203
