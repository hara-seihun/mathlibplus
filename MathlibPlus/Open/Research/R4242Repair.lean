import MathlibPlus.Open.Research.R4242

namespace MathlibPlus.Open.Research.R4242Repair

abbrev RepairB := R4242.B
abbrev RepairPoint (m : ℕ) := R4242.FibrePoint m

def repairSourceCycle : Equiv.Perm RepairB :=
  Equiv.swap (0 : RepairB) 7 * Equiv.swap 0 6 * Equiv.swap 0 5 *
    Equiv.swap 0 4 * Equiv.swap 0 3 * Equiv.swap 0 2 * Equiv.swap 0 1

def repairTargetCycle : Equiv.Perm RepairB :=
  Equiv.swap (0 : RepairB) 3 * Equiv.swap 0 2 * Equiv.swap 0 5 *
    Equiv.swap 0 4 * Equiv.swap 0 7 * Equiv.swap 0 6 * Equiv.swap 0 1

def repairSourceC8 : Subgroup (Equiv.Perm RepairB) :=
  Subgroup.closure ({repairSourceCycle} : Set (Equiv.Perm RepairB))

def repairTargetC8 : Subgroup (Equiv.Perm RepairB) :=
  Subgroup.closure ({repairTargetCycle} : Set (Equiv.Perm RepairB))

def repairQuotientAction : Subgroup (Equiv.Perm RepairB) :=
  R4242.generatedCopy repairSourceCycle repairTargetCycle

def repairQuotientConjugates (q : Equiv.Perm RepairB) : Prop :=
  ∀ g : Equiv.Perm RepairB,
    g ∈ repairSourceC8 ↔ q⁻¹ * g * q ∈ repairTargetC8

def repairIdentityFixedQuotientTransporter
    (q : Equiv.Perm RepairB) : Prop :=
  q 0 = 0 ∧ repairQuotientConjugates q

def repairQ1Tuple (q : RepairB → RepairB) : Prop :=
  ∀ j, q j = R4242.q1Map j

def repairQ2Tuple (q : RepairB → RepairB) : Prop :=
  ∀ j, q j = R4242.q2Map j

def repairQ3Tuple (q : RepairB → RepairB) : Prop :=
  ∀ j, q j = R4242.q3Map j

def repairQ4Tuple (q : RepairB → RepairB) : Prop :=
  ∀ j, q j = R4242.q4Map j

def repairDisplayedQuotientMap (q : RepairB → RepairB) : Prop :=
  repairQ1Tuple q ∨ repairQ2Tuple q ∨ repairQ3Tuple q ∨ repairQ4Tuple q

def repairQuotientTransporters : Set (Equiv.Perm RepairB) :=
  {q | repairIdentityFixedQuotientTransporter q}

def claim53498 : Prop :=
  repairQuotientTransporters =
      ({q : Equiv.Perm RepairB |
          repairDisplayedQuotientMap (q : RepairB → RepairB)} :
        Set (Equiv.Perm RepairB)) ∧
    ∀ q : Equiv.Perm RepairB,
      repairDisplayedQuotientMap (q : RepairB → RepairB) →
        R4242.fixesAllUnorderedOrbitals repairQuotientAction q

def repairBlockStabilizer : Set (Equiv.Perm RepairB) :=
  {g | g ∈ repairQuotientAction ∧ g (0 : RepairB) = 0}

def repairH : Equiv.Perm RepairB :=
  Equiv.swap (1 : RepairB) 5 * Equiv.swap 3 7

def repairPointStabilizerSuborbit (m : ℕ)
    (X : Subgroup (Equiv.Perm (RepairPoint m)))
    (x : RepairPoint m) : Set (RepairPoint m) :=
  {y | ∃ g : X,
    (g : Equiv.Perm (RepairPoint m)) (0, 0) = (0, 0) ∧
      (g : Equiv.Perm (RepairPoint m)) x = y}

def repairInverseCoordinate (m : ℕ) (z : RepairPoint m) : RepairPoint m :=
  (-z.1,
    -(if z.1.val % 2 = 0 then (1 : ZMod m) else -1) * z.2)

def repairInversePairedSuborbit (m : ℕ)
    (X : Subgroup (Equiv.Perm (RepairPoint m)))
    (x : RepairPoint m) : Set (RepairPoint m) :=
  repairPointStabilizerSuborbit m X x ∪
    repairPointStabilizerSuborbit m X (repairInverseCoordinate m x)

def repairOzero (m : ℕ) (r : ZMod m) : Set (RepairPoint m) :=
  {(0, r), (0, -r)}

def repairOfour (m : ℕ) (r : ZMod m) : Set (RepairPoint m) :=
  {(4, r), (4, -r)}

def repairOodd (m : ℕ) (r : ZMod m) : Set (RepairPoint m) :=
  {(1, r), (3, r), (5, r), (7, r)}

def repairOtwosix (m : ℕ) (r : ZMod m) : Set (RepairPoint m) :=
  {(2, r), (6, -r)}

def claim53499 : Prop :=
  ∀ m : ℕ, 1 < m → Odd m →
    ∀ a bs bt : Equiv.Perm (RepairPoint m),
      R4242.copySetup m a bs bt →
        let R := R4242.generatedCopy a bs
        let T := R4242.generatedCopy a bt
        let X := R4242.generatedPair R T
        repairBlockStabilizer =
            (Subgroup.closure ({repairH} : Set (Equiv.Perm RepairB)) :
              Set (Equiv.Perm RepairB)) ∧
          ∀ r : ZMod m,
            repairOzero m r =
                repairInversePairedSuborbit m X (0, r) ∧
              repairOfour m r =
                repairInversePairedSuborbit m X (4, r) ∧
              repairOodd m r =
                repairInversePairedSuborbit m X (1, r) ∧
              repairOtwosix m r =
                repairInversePairedSuborbit m X (2, r)

def repairCompatibleLift (m : ℕ)
    (R T : Subgroup (Equiv.Perm (RepairPoint m)))
    (X : Subgroup (Equiv.Perm (RepairPoint m)))
    (q : RepairB → RepairB)
    (c : Equiv.Perm (RepairPoint m)) : Prop :=
  R4242.fibreTrivialLift q c ∧
    R4242.conjugates R T c ∧
    R4242.fixesAllUnorderedOrbitals X c

def claim53500 : Prop :=
  ∀ m : ℕ, 1 < m → Odd m →
    ∀ a bs bt : Equiv.Perm (RepairPoint m),
      R4242.copySetup m a bs bt →
        let R := R4242.generatedCopy a bs
        let T := R4242.generatedCopy a bt
        let X := R4242.generatedPair R T
        (∃ c, repairCompatibleLift m R T X R4242.q2Map c) ∧
          (∃ c, repairCompatibleLift m R T X R4242.q4Map c) ∧
          R4242.q2Map ≠ R4242.q4Map

def repairParity (m : ℕ) (j : RepairB) : ZMod m :=
  ((j.val % 2 : ℕ) : ZMod m)

def repairFullCopyConjugator (m : ℕ)
    (R T : Subgroup (Equiv.Perm (RepairPoint m)))
    (q : RepairB → RepairB)
    (c : Equiv.Perm (RepairPoint m)) : Prop :=
  R4242.identityFixed c ∧
    R4242.inducesBlock q c ∧
    R4242.conjugates R T c

def claim53501 : Prop :=
  ∀ m : ℕ, 1 < m → Odd m →
    ∀ a bs bt : Equiv.Perm (RepairPoint m),
      R4242.copySetup m a bs bt →
        let R := R4242.generatedCopy a bs
        let T := R4242.generatedCopy a bt
        ∀ q : RepairB → RepairB,
          (repairQ1Tuple q ∨ repairQ3Tuple q) →
            ∀ c : Equiv.Perm (RepairPoint m),
              repairFullCopyConjugator m R T q c →
                ∃ u : (ZMod m)ˣ, ∃ v : ZMod m,
                  ∀ j x,
                    c (j, x) =
                      (q j, (u : ZMod m) * x + repairParity m j * v)

end MathlibPlus.Open.Research.R4242Repair
