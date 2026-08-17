import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.R0982Claim27886

abbrev Plane (p : ℕ) := ZMod p × ZMod p
abbrev Fiber (p : ℕ) := Fin 3 → ZMod p
abbrev H (p : ℕ) := Plane p × Fiber p
abbrev E (p : ℕ) := ZMod p × H p

private def quadraticF (p : ℕ) (u : Plane p) : Fiber p :=
  ![u.1 * (u.1 - 1), ((2 : ZMod p) * u.1 - 1) * u.2, u.2 ^ 2]

private def polarDerivativeF (p : ℕ) (u c : Plane p) : Fiber p :=
  ![(2 : ZMod p) * c.1 * u.1,
    (2 : ZMod p) * c.1 * u.2 + (2 : ZMod p) * c.2 * u.1,
    (2 : ZMod p) * c.2 * u.2]

private def derivativePhi (p : ℕ) (φ : Plane p → ZMod p)
    (u c : Plane p) : ZMod p :=
  φ (u + c) - φ u - φ c

private def quietAt (p : ℕ) (φ : Plane p → ZMod p)
    (u : Plane p) : Prop :=
  (∀ c d : Plane p,
    derivativePhi p φ u (c + d) =
      derivativePhi p φ u c + derivativePhi p φ u d) ∧
    (∀ a : ZMod p, ∀ c : Plane p,
      derivativePhi p φ u (a • c) = a • derivativePhi p φ u c)

private def quietLocus (p : ℕ) (φ : Plane p → ZMod p) : Set (Plane p) :=
  {u | quietAt p φ u}

private def displayedGraphVector (p : ℕ) (φ : Plane p → ZMod p)
    (u c : Plane p) : ZMod p × Fiber p :=
  (derivativePhi p φ u c, polarDerivativeF p u c)

private def graphSpan (p : ℕ) (φ : Plane p → ZMod p)
    (u : Plane p) : Submodule (ZMod p) (ZMod p × Fiber p) :=
  Submodule.span (ZMod p)
    (Set.range (fun c : Plane p => displayedGraphVector p φ u c))

private def displacementPlane (p : ℕ) (u : Plane p) :
    Submodule (ZMod p) (Fiber p) :=
  Submodule.span (ZMod p)
    ({![u.1, u.2, 0], ![0, u.1, u.2]} : Set (Fiber p))

private def fiberDirectSum (p : ℕ) (u : Plane p) :
    Submodule (ZMod p) (ZMod p × Fiber p) :=
  (⊤ : Submodule (ZMod p) (ZMod p)).prod
    (displacementPlane p u)

private def translationSubgroup (V : Type*) [AddGroup V] :
    Subgroup (Equiv.Perm V) :=
  Subgroup.closure
    (Set.range (fun v : V => (Equiv.addRight v : Equiv.Perm V)))

private def conjugatedTranslations {V : Type*}
    (q : Equiv.Perm V) (T : Subgroup (Equiv.Perm V)) :
    Set (Equiv.Perm V) :=
  {u | ∃ t : T, u = q⁻¹ * (t : Equiv.Perm V) * q}

private def generatedGroup (p : ℕ) (q : Equiv.Perm (E p)) :
    Subgroup (Equiv.Perm (E p)) :=
  Subgroup.closure
    ((translationSubgroup (E p) : Set (Equiv.Perm (E p))) ∪
      conjugatedTranslations q (translationSubgroup (E p)))

private def qPhiSpec (p : ℕ) (φ : Plane p → ZMod p)
    (q : Equiv.Perm (E p)) : Prop :=
  ∀ z u w,
    q (z, (u, w)) =
      (z + φ u, (u, w + quadraticF p u))

private def relativeDerivativePoint (p : ℕ) (q : Equiv.Perm (E p))
    (u c : Plane p) : E p :=
  q⁻¹ (q (0, (u + c, 0)) - q (0, (u, 0)))

private def relativeDerivativeGraphVector
    (p : ℕ) (q : Equiv.Perm (E p)) (u c : Plane p) :
    ZMod p × Fiber p :=
  let d := relativeDerivativePoint p q u c
  (d.1, d.2.2)

private def relativeGraphSpan (p : ℕ) (q : Equiv.Perm (E p))
    (u : Plane p) : Submodule (ZMod p) (ZMod p × Fiber p) :=
  Submodule.span (ZMod p)
    (Set.range (fun c : Plane p =>
      relativeDerivativeGraphVector p q u c))

private def pointStabilizerSuborbit
    (G : Subgroup (Equiv.Perm (E p))) (x : E p) : Set (E p) :=
  {y | ∃ h : G,
    (h : Equiv.Perm (E p)) 0 = 0 ∧
      (h : Equiv.Perm (E p)) x = y}

private def saturatedSuborbit (p : ℕ) (u : Plane p) : Set (E p) :=
  {y | y.2.1 = u ∧ y.2.2 ∈ displacementPlane p u}

private def fiberCorrection (p : ℕ) (ell : Plane p → ZMod p) :
    E p → E p :=
  fun y => (y.1 + ell y.2.1, y.2)

private def noCorrectionCondition
    (p : ℕ) (G : Subgroup (Equiv.Perm (E p))) (u : Plane p) : Prop :=
  ∀ ell : Plane p → ZMod p,
    Set.image (fiberCorrection p ell)
        (pointStabilizerSuborbit G (0, (u, 0))) =
      pointStabilizerSuborbit G (0, (u, 0))

/-- Claim 27886: outside the quiet locus, the displayed relative-derivative
 graph fills the whole first fibre coordinate together with the exact plane
 W_u, so the actual point-stabilizer suborbit has no correction constraint. -/
def claim27886_saturationOutsideQuietLocus : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p) (_hodd : Odd p),
    letI : Fact p.Prime := ⟨hp⟩
    ∀ (φ : Plane p → ZMod p), φ 0 = 0 →
      ∃ q : Equiv.Perm (E p),
        qPhiSpec p φ q ∧
        (∀ u : Plane p, u ∉ quietLocus p φ →
          let G := generatedGroup p q
          (∀ c : Plane p,
            relativeDerivativeGraphVector p q u c =
              displayedGraphVector p φ u c) ∧
          relativeGraphSpan p q u = fiberDirectSum p u ∧
          graphSpan p φ u = fiberDirectSum p u ∧
          pointStabilizerSuborbit G (0, (u, 0)) =
            saturatedSuborbit p u ∧
          noCorrectionCondition p G u)

end MathlibPlus.Open.ResearchFormalization.R0982Claim27886
