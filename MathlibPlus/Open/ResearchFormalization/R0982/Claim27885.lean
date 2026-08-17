import MathlibPlus.Open.Research.OrbitalCriteria

namespace MathlibPlus.Open.ResearchFormalization.R0982

noncomputable section

abbrev Plane (p : ℕ) := ZMod p × ZMod p
abbrev Fiber (p : ℕ) := ZMod p × ZMod p × ZMod p
abbrev Omega (p : ℕ) := ZMod p × Plane p × Fiber p

def quadraticF (p : ℕ) (u : Plane p) : Fiber p :=
  (u.1 * (u.1 - 1), ((2 : ZMod p) * u.1 - 1) * u.2, u.2 ^ 2)

def polarDerivative (p : ℕ) (u c : Plane p) : Fiber p :=
  quadraticF p (u + c) - quadraticF p u - quadraticF p c

def planeDerivative (p : ℕ) (φ : Plane p → ZMod p)
    (u c : Plane p) : ZMod p :=
  φ (u + c) - φ u - φ c

def quietAt (p : ℕ) (φ : Plane p → ZMod p)
    (u : Plane p) : Prop :=
  (∀ c d : Plane p,
    planeDerivative p φ u (c + d) =
      planeDerivative p φ u c + planeDerivative p φ u d) ∧
  (∀ a : ZMod p, ∀ c : Plane p,
    planeDerivative p φ u (a • c) =
      a • planeDerivative p φ u c)

def quietLocus (p : ℕ) (φ : Plane p → ZMod p) : Set (Plane p) :=
  {u | quietAt p φ u}

def quietCorrection (p : ℕ) (φ : Plane p → ZMod p)
    (u : Plane p) : ZMod p :=
  planeDerivative p φ u
    ((u.1 - 1) * (2 : ZMod p)⁻¹, u.2 * (2 : ZMod p)⁻¹) - φ u

def quietRemainder (p : ℕ) (φ : Plane p → ZMod p)
    (u : Plane p) : ZMod p :=
  φ u - planeDerivative p φ u u * (2 : ZMod p)⁻¹

def qPhiFunction (p : ℕ) (φ : Plane p → ZMod p) :
    Omega p → Omega p :=
  fun x =>
    (x.1 + φ x.2.1, x.2.1, x.2.2 + quadraticF p x.2.1)

def isQPhi (p : ℕ) (φ : Plane p → ZMod p)
    (q : Equiv.Perm (Omega p)) : Prop :=
  ∀ x, q x = qPhiFunction p φ x

def planeFiberGroup (p : ℕ) (q : Equiv.Perm (Omega p)) :
    Subgroup (Equiv.Perm (Omega p)) :=
  Subgroup.closure
    ((MathlibPlus.Open.Research.OrbitalCriteria.translationSet :
        Set (Equiv.Perm (Omega p))) ∪
      MathlibPlus.Open.Research.OrbitalCriteria.conjugateSet q
        (MathlibPlus.Open.Research.OrbitalCriteria.translationSet :
          Set (Equiv.Perm (Omega p))))

def claim27885 : Prop :=
  ∀ (p : ℕ), Nat.Prime p → Odd p →
    ∀ (φ : Plane p → ZMod p), φ 0 = 0 →
      (∀ u : Plane p, polarDerivative p u
          ((u.1 - 1) * (2 : ZMod p)⁻¹, u.2 * (2 : ZMod p)⁻¹) =
          quadraticF p u) ∧
      (∀ u : Plane p, u ≠ 0 →
        ∀ c : Plane p,
          polarDerivative p u c = quadraticF p u →
            c = ((u.1 - 1) * (2 : ZMod p)⁻¹,
              u.2 * (2 : ZMod p)⁻¹)) ∧
      ∃ qφ : Equiv.Perm (Omega p),
        isQPhi p φ qφ ∧
        ∃ ell : Plane p →ₗ[ZMod p] ZMod p,
          (∀ u : Plane p, u ∈ quietLocus p φ →
            ell u = quietCorrection p φ u) ∧
          ∃ qc : Equiv.Perm (Omega p),
            isQPhi p (fun u => φ u + ell u) qc ∧
            qc 0 = 0 ∧
            MathlibPlus.Open.Research.OrbitalCriteria.fixesStabilizerOrbits
              qc (planeFiberGroup p qφ : Set (Equiv.Perm (Omega p))) 0 ∧
            qc ∈ MathlibPlus.Open.Research.OrbitalCriteria.twoClosureOf
              (planeFiberGroup p qφ : Set (Equiv.Perm (Omega p))) ∧
            MathlibPlus.Open.Research.OrbitalCriteria.conjugateSet qc
                (MathlibPlus.Open.Research.OrbitalCriteria.translationSet :
                  Set (Equiv.Perm (Omega p))) =
              MathlibPlus.Open.Research.OrbitalCriteria.conjugateSet qφ
                (MathlibPlus.Open.Research.OrbitalCriteria.translationSet :
                  Set (Equiv.Perm (Omega p)))

end
end MathlibPlus.Open.ResearchFormalization.R0982
