import Mathlib

namespace MathlibPlus.Open.Research.R4241Corrected

abbrev C8 := ZMod 8
abbrev AffinePoint (n : ℕ) := ZMod n × C8

def oddSquarefree (n : ℕ) : Prop :=
  0 < n ∧ Odd n ∧ ∀ p : ℕ, p.Prime → ¬ p ^ 2 ∣ n

def evenCoordinate (h : C8) : Prop :=
  h.val % 2 = 0

def epsilon (n : ℕ) (h : C8) : ZMod n :=
  if h.val % 2 = 0 then 0 else 1

def parityCharacter (n : ℕ) (h : C8) : ZMod n :=
  if h.val % 2 = 0 then 1 else -1

def integerParityCharacter (h : C8) : ℤ :=
  if h.val % 2 = 0 then 1 else -1

def affineMul (n : ℕ) (a b : AffinePoint n) : AffinePoint n :=
  (a.1 + parityCharacter n a.2 * b.1, a.2 + b.2)

def cycle2 (a b : C8) : Equiv.Perm C8 :=
  Equiv.swap a b

def cycle3 (a b c : C8) : Equiv.Perm C8 :=
  cycle2 a b * cycle2 b c

def cycle4 (a b c d : C8) : Equiv.Perm C8 :=
  cycle2 a b * cycle2 b c * cycle2 c d

def seedSeven : Equiv.Perm C8 :=
  cycle2 0 1 * cycle2 1 6 * cycle2 6 7 * cycle2 7 4 *
    cycle2 4 5 * cycle2 5 2 * cycle2 2 3

def seedSixteen : Equiv.Perm C8 :=
  cycle2 0 5 * cycle2 5 2 * cycle2 2 3 * cycle2 3 4 *
    cycle2 4 1 * cycle2 1 6 * cycle2 6 7

def seedPermutation (s : Fin 2) : Equiv.Perm C8 :=
  if s.1 = 0 then seedSeven else seedSixteen

def phaseUnit (u : Fin 4) : C8 :=
  ((2 * u.1 + 1 : ℕ) : C8)

def terminalTransporterValue (s : Fin 2) (u : Fin 4) (h : C8) : C8 :=
  ((seedPermutation s) ^ ((phaseUnit u * h).val)) 0

def terminalSevenUnitOne : Equiv.Perm C8 :=
  cycle2 2 6 * cycle2 3 7

def terminalSevenUnitThree : Equiv.Perm C8 :=
  cycle4 1 7 5 3

def terminalSevenUnitFive : Equiv.Perm C8 :=
  cycle2 1 5 * cycle2 2 6

def terminalSevenUnitSeven : Equiv.Perm C8 :=
  cycle4 1 3 5 7

def terminalSixteenUnitOne : Equiv.Perm C8 :=
  cycle2 1 5

def terminalSixteenUnitThree : Equiv.Perm C8 :=
  cycle4 1 3 5 7 * cycle2 2 6

def terminalSixteenUnitFive : Equiv.Perm C8 :=
  cycle2 3 7

def terminalSixteenUnitSeven : Equiv.Perm C8 :=
  cycle4 1 7 5 3 * cycle2 2 6

def terminalMap (s : Fin 2) (u : Fin 4) : Equiv.Perm C8 :=
  if s.1 = 0 then
    if u.1 = 0 then terminalSevenUnitOne
    else if u.1 = 1 then terminalSevenUnitThree
    else if u.1 = 2 then terminalSevenUnitFive
    else terminalSevenUnitSeven
  else
    if u.1 = 0 then terminalSixteenUnitOne
    else if u.1 = 1 then terminalSixteenUnitThree
    else if u.1 = 2 then terminalSixteenUnitFive
    else terminalSixteenUnitSeven

def shadowMultiplier (s : Fin 2) (u : Fin 4) : C8 :=
  if s.1 = 0 then 3 * phaseUnit u else phaseUnit u

def shadowFunction (s : Fin 2) (u : Fin 4) (h : C8) : C8 :=
  shadowMultiplier s u * h

def multiplierThree : Equiv.Perm C8 :=
  cycle2 1 3 * cycle2 2 6 * cycle2 5 7

def multiplierFive : Equiv.Perm C8 :=
  cycle2 1 5 * cycle2 3 7

def multiplierSeven : Equiv.Perm C8 :=
  cycle2 1 7 * cycle2 2 6 * cycle2 3 5

def shadowMap (s : Fin 2) (u : Fin 4) : Equiv.Perm C8 :=
  if s.1 = 0 then
    if u.1 = 0 then multiplierThree
    else if u.1 = 1 then (Equiv.refl C8)
    else if u.1 = 2 then multiplierSeven
    else multiplierFive
  else
    if u.1 = 0 then (Equiv.refl C8)
    else if u.1 = 1 then multiplierThree
    else if u.1 = 2 then multiplierFive
    else multiplierSeven

def affineShadow (n : ℕ) (c : ZMod n) (s : Fin 2) (u : Fin 4)
    (z : AffinePoint n) : AffinePoint n :=
  (z.1 + c * epsilon n z.2, shadowFunction s u z.2)

def normalizedBlockwiseAffineLift
    (n : ℕ) (s : Fin 2) (u : Fin 4)
    (f : AffinePoint n → AffinePoint n)
    (lambda : C8 → (ZMod n)ˣ) (tau : C8 → ZMod n) : Prop :=
  lambda 0 = 1 ∧ tau 0 = 0 ∧
    ∀ x h, f (x, h) =
      ((lambda h : ZMod n) * x + tau h, terminalMap s u h)

def terminalDerivative
    (q : Equiv.Perm C8) (k h : C8) : C8 :=
  q.symm (q (h + k) - q k)

def relativeDerivative
    {n : ℕ} (q : Equiv.Perm C8)
    (lambda : C8 → (ZMod n)ˣ) (tau : C8 → ZMod n)
    (k h : C8) (x y : ZMod n) : AffinePoint n :=
  let d := terminalDerivative q k h
  ( ((lambda (h + k) : ZMod n) * x
      + parityCharacter n h *
          ((lambda (h + k) : ZMod n) - (lambda k : ZMod n)) * y
      + tau (h + k) - parityCharacter n h * tau k - tau d) *
        (↑((lambda d)⁻¹) : ZMod n),
    d )

def sourceInversion {n : ℕ} (z : AffinePoint n) : AffinePoint n :=
  (-parityCharacter n z.2 * z.1, -z.2)

def transportedInversion
    {n : ℕ} (q : Equiv.Perm C8)
    (lambda : C8 → (ZMod n)ˣ) (tau : C8 → ZMod n)
    (z : AffinePoint n) : AffinePoint n :=
  let j := q z.2
  let d := q.symm (-j)
  ( (-parityCharacter n j *
          ((lambda z.2 : ZMod n) * z.1 + tau z.2) - tau d) *
        (↑((lambda d)⁻¹) : ZMod n),
    d )

def actionEdge
    {n : ℕ} (q : Equiv.Perm C8)
    (lambda : C8 → (ZMod n)ˣ) (tau : C8 → ZMod n)
    (a b : AffinePoint n) : Prop :=
  (∃ k y, relativeDerivative q lambda tau k a.2 a.1 y = b) ∨
  transportedInversion q lambda tau a = b ∨
  sourceInversion a = b ∨
  (∃ k y, relativeDerivative q lambda tau k b.2 b.1 y = a) ∨
  transportedInversion q lambda tau b = a ∨
  sourceInversion b = a

def generatedOrbit
    {n : ℕ} (q : Equiv.Perm C8)
    (lambda : C8 → (ZMod n)ˣ) (tau : C8 → ZMod n)
    (a b : AffinePoint n) : Prop :=
  Relation.ReflTransGen (actionEdge q lambda tau) a b

def globalBaseFibre
    {n : ℕ} (q : Equiv.Perm C8)
    (lambda : C8 → (ZMod n)ˣ) (tau : C8 → ZMod n) (h : C8) : Set (ZMod n) :=
  {x | generatedOrbit q lambda tau (0, h) (x, h)}

def globalFullFibre
    {n : ℕ} (q : Equiv.Perm C8)
    (lambda : C8 → (ZMod n)ˣ) (tau : C8 → ZMod n) (h : C8) : Prop :=
  globalBaseFibre q lambda tau h = Set.univ

def scalarStabilizer {n : ℕ}
    (lambda : C8 → (ZMod n)ˣ) : Set C8 :=
  {a | ∀ k, lambda (a + k) = lambda k}

def c4Layer : Set C8 :=
  {0, 2, 4, 6}

def oneScalar {n : ℕ} : C8 → (ZMod n)ˣ :=
  fun _ => 1

def zeroShift {n : ℕ} : C8 → ZMod n :=
  fun _ => 0

def qLayerActionEdge
    {n : ℕ} (q : Equiv.Perm C8)
    (lambda : C8 → (ZMod n)ˣ) (tau : C8 → ZMod n)
    (Q : Set C8) (a b : AffinePoint n) : Prop :=
  (∃ k y, k ∈ Q ∧
    relativeDerivative q lambda tau k a.2 a.1 y = b) ∨
  transportedInversion q lambda tau a = b ∨
  sourceInversion a = b ∨
  (∃ k y, k ∈ Q ∧
    relativeDerivative q lambda tau k b.2 b.1 y = a) ∨
  transportedInversion q lambda tau b = a ∨
  sourceInversion b = a

def qLayerOrbit
    {n : ℕ} (q : Equiv.Perm C8)
    (lambda : C8 → (ZMod n)ˣ) (tau : C8 → ZMod n)
    (Q : Set C8) (a b : AffinePoint n) : Prop :=
  a.2 ∈ Q ∧ b.2 ∈ Q ∧
    Relation.ReflTransGen (qLayerActionEdge q lambda tau Q) a b

def qLayerBaseFibre
    {n : ℕ} (q : Equiv.Perm C8)
    (lambda : C8 → (ZMod n)ˣ) (tau : C8 → ZMod n)
    (Q : Set C8) (h : C8) : Set (ZMod n) :=
  {x | qLayerOrbit q lambda tau Q (0, h) (x, h)}

def qLayerQuietFibre
    {n : ℕ} (q : Equiv.Perm C8)
    (lambda : C8 → (ZMod n)ˣ) (tau : C8 → ZMod n)
    (Q : Set C8) (h : C8) : Prop :=
  qLayerBaseFibre q lambda tau Q h = ({0} : Set (ZMod n))

def qLayerFullFibre
    {n : ℕ} (q : Equiv.Perm C8)
    (lambda : C8 → (ZMod n)ˣ) (tau : C8 → ZMod n)
    (Q : Set C8) (h : C8) : Prop :=
  qLayerBaseFibre q lambda tau Q h = Set.univ

def pointwiseShadowedOnQ
    {n : ℕ} (f : AffinePoint n → AffinePoint n)
    (q : Equiv.Perm C8)
    (lambda : C8 → (ZMod n)ˣ) (tau : C8 → ZMod n)
    (Q : Set C8) (alpha : Equiv.Perm (AffinePoint n)) : Prop :=
  ∀ h, h ∈ Q → qLayerQuietFibre q lambda tau Q h →
    ∀ x : ZMod n, f (x, h) = alpha (x, h)

def claim53486 : Prop :=
  ∀ n : ℕ, oddSquarefree n →
    ∀ s : Fin 2, ∀ u : Fin 4,
    ∀ f : AffinePoint n → AffinePoint n,
    ∀ lambda : C8 → (ZMod n)ˣ, ∀ tau : C8 → ZMod n,
      normalizedBlockwiseAffineLift n s u f lambda tau →
      let Q := scalarStabilizer lambda
      Q ⊂ (Set.univ : Set C8) →
        Q ⊆ c4Layer ∧
        (∀ a : C8, a ∈ Q → parityCharacter n a = 1) ∧
        (∀ a : C8, a ∈ Q → terminalMap s u a = shadowFunction s u a) ∧
        (∃ alpha : Equiv.Perm (AffinePoint n),
          (∀ z, alpha z = affineShadow n 0 s u z) ∧
          pointwiseShadowedOnQ f (terminalMap s u) lambda tau Q alpha ∧
          (∀ h : C8, h ∈ Q →
            ¬ qLayerQuietFibre (terminalMap s u) lambda tau Q h →
              qLayerFullFibre (terminalMap s u) lambda tau Q h) ∧
          (∀ h : C8, h ∉ Q →
            globalFullFibre (terminalMap s u) lambda tau h))

def derivativeTranslationGain
    {n : ℕ} (q : Equiv.Perm C8) (tau : C8 → ZMod n)
    (h k : C8) : ZMod n :=
  tau (h + k) - parityCharacter n h * tau k -
    tau (terminalDerivative q k h)

def inversionTranslationGain
    {n : ℕ} (q : Equiv.Perm C8) (tau : C8 → ZMod n)
    (h : C8) : ZMod n :=
  let j := q h
  let d := q.symm (-j)
  (-parityCharacter n j * tau h - tau d)

def integralDerivativeGain
    (q : Equiv.Perm C8) (tauInt : C8 → ℤ) (h k : C8) : ℤ :=
  tauInt (h + k) - integerParityCharacter h * tauInt k -
    tauInt (terminalDerivative q k h)

def integralInversionGain
    (q : Equiv.Perm C8) (tauInt : C8 → ℤ) (h : C8) : ℤ :=
  let j := q h
  let d := q.symm (-j)
  (-integerParityCharacter j * tauInt h - tauInt d)

def hasSignedIntegralTranslationGains
    {n : ℕ} (q : Equiv.Perm C8) (tau : C8 → ZMod n) : Prop :=
  ∃ tauInt : C8 → ℤ,
    tauInt 0 = 0 ∧
    (∀ h, (tauInt h : ZMod n) = tau h) ∧
    (∀ h k,
      (integralDerivativeGain q tauInt h k : ZMod n) =
        derivativeTranslationGain q tau h k) ∧
    (∀ h,
      (integralInversionGain q tauInt h : ZMod n) =
        inversionTranslationGain q tau h)

def claim53487 : Prop :=
  ∀ n : ℕ, oddSquarefree n →
    ∀ s : Fin 2, ∀ u : Fin 4,
    ∀ f : AffinePoint n → AffinePoint n,
    ∀ lambda : C8 → (ZMod n)ˣ, ∀ tau : C8 → ZMod n,
      normalizedBlockwiseAffineLift n s u f lambda tau →
      scalarStabilizer lambda = (Set.univ : Set C8) →
        (∀ h : C8, lambda h = 1) ∧
        hasSignedIntegralTranslationGains (terminalMap s u) tau

def componentFibre
    {n : ℕ} (q : Equiv.Perm C8) (tau : C8 → ZMod n)
    (A : Set C8) : Set (ZMod n) :=
  {z | ∃ h h' : C8, h ∈ A ∧ h' ∈ A ∧
    generatedOrbit q (oneScalar (n := n)) tau (0, h) (z, h')}

def quietComponent
    {n : ℕ} (q : Equiv.Perm C8) (tau : C8 → ZMod n)
    (A : Set C8) : Prop :=
  componentFibre q tau A = ({0} : Set (ZMod n))

def fullComponent
    {n : ℕ} (q : Equiv.Perm C8) (tau : C8 → ZMod n)
    (A : Set C8) : Prop :=
  componentFibre q tau A = Set.univ

def oddAtom : Set C8 :=
  {1, 3, 5, 7}

def twoSixAtom : Set C8 :=
  {2, 6}

def centralAtom : Set C8 :=
  {4}

def noncentralQuiet
    {n : ℕ} (q : Equiv.Perm C8) (tau : C8 → ZMod n) : Prop :=
  quietComponent q tau oddAtom ∧ quietComponent q tau twoSixAtom

def noncentralFull
    {n : ℕ} (q : Equiv.Perm C8) (tau : C8 → ZMod n) : Prop :=
  fullComponent q tau oddAtom ∧ fullComponent q tau twoSixAtom

def parityShiftProfile {n : ℕ} (tau : C8 → ZMod n) : Prop :=
  ∃ c : ZMod n, ∀ h : C8, tau h = c * epsilon n h

def claim53489 : Prop :=
  ∀ p : ℕ, (p.Prime ∧ Odd p) →
    ∀ s : Fin 2, ∀ u : Fin 4, ∀ tau : C8 → ZMod p,
      tau 0 = 0 →
        (noncentralQuiet (terminalMap s u) tau ↔
          parityShiftProfile tau) ∧
        (¬ parityShiftProfile tau →
          noncentralFull (terminalMap s u) tau)

def centralQuiet
    {n : ℕ} (q : Equiv.Perm C8) (tau : C8 → ZMod n) : Prop :=
  quietComponent q tau centralAtom

def centralFull
    {n : ℕ} (q : Equiv.Perm C8) (tau : C8 → ZMod n) : Prop :=
  fullComponent q tau centralAtom

def claim53490 : Prop :=
  ∀ n : ℕ, oddSquarefree n →
    ∀ s : Fin 2, ∀ u : Fin 4, ∀ tau : C8 → ZMod n,
      tau 0 = 0 →
        (centralQuiet (terminalMap s u) tau →
          tau (4 : C8) = 0 ∧
          tau ((1 : C8) + 4) = tau 1 ∧
          tau ((2 : C8) + 4) = tau 2 ∧
          tau ((3 : C8) + 4) = tau 3) ∧
        (¬ centralQuiet (terminalMap s u) tau →
          centralFull (terminalMap s u) tau)

end MathlibPlus.Open.Research.R4241Corrected
