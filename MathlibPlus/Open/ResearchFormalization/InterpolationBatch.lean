import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization

/-- The prefix node list with one new node appended. -/
def appendNodes {n : ℕ} (nodes : Fin n → ℝ) (y : ℝ) : Fin (n + 1) → ℝ :=
  fun i => if h : i.1 < n then nodes ⟨i.1, h⟩ else y

/-- Values on an appended prefix, using the value at the new node. -/
def appendValues {n : ℕ} {α : Type} (values : Fin n → α) (lastValue : α) : Fin (n + 1) → α :=
  fun i => if h : i.1 < n then values ⟨i.1, h⟩ else lastValue

/-- The monic node product. -/
def nodeProduct {n : ℕ} (nodes : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∏ i : Fin n, (t - nodes i)

/-- The cardinal function associated with one node. -/
def cardinal {n : ℕ} (nodes : Fin n → ℝ) (i : Fin n) (t : ℝ) : ℝ :=
  ∏ j : Fin n, if j = i then 1 else (t - nodes j) / (nodes i - nodes j)

/-- The interpolant and its Lebesgue function. -/
def interpolant {n : ℕ} (nodes : Fin n → ℝ) (values : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ i : Fin n, values i * cardinal nodes i t

def lebesgue {n : ℕ} (nodes : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ i : Fin n, |cardinal nodes i t|

/-- The product occurring in the derivative of the node polynomial at a node. -/
def derivativeProduct {n : ℕ} (nodes : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∏ j ∈ (Finset.univ.erase i), (nodes i - nodes j)

def normalization {n : ℕ} (nodes : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, 1 / |derivativeProduct nodes i|

def prefixNodes (x : ℕ → ℝ) (n : ℕ) : Fin n → ℝ :=
  fun i => x i.1

def prefixInterpolant (x : ℕ → ℝ) (n : ℕ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  interpolant (prefixNodes x n) (fun i => f (x i.1)) t

def prefixLebesgue (x : ℕ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  lebesgue (prefixNodes x n) t

def interpolationIncrement (x : ℕ → ℝ) (n : ℕ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  prefixInterpolant x (n + 1) f t - prefixInterpolant x n f t

def pointEvaluationNormOfIncrement (x : ℕ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (∑ i : Fin n,
      |cardinal (appendNodes (prefixNodes x n) (x n)) (Fin.castSucc i) t -
        cardinal (prefixNodes x n) i t|) +
    |cardinal (appendNodes (prefixNodes x n) (x n)) (Fin.last n) t|

def qWeight {n : ℕ} (nodes : Fin n → ℝ) (i : Fin n) : ℝ :=
  1 / (normalization nodes * |derivativeProduct nodes i|)

def signedEpsilon (n : ℕ) (i : Fin n) : ℝ :=
  (-1 : ℝ) ^ (n - (i.1 + 1))

def vandermonde {n : ℕ} (nodes : Fin n → ℝ) : ℝ :=
  ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (nodes j - nodes i)

/-- Exact nested interpolation insertion formula and its new-cardinal lower bound. -/
def claim36105 : Prop :=
  ∀ (n : ℕ) (nodes : Fin n → ℝ) (f : ℝ → ℝ) (y t : ℝ),
    Function.Injective nodes →
    (∀ i : Fin n, y ≠ nodes i) →
      interpolant (appendNodes nodes y)
          (appendValues (fun i => f (nodes i)) (f y)) t =
        interpolant nodes (fun i => f (nodes i)) t +
          (f y - interpolant nodes (fun i => f (nodes i)) y) *
            nodeProduct nodes t / nodeProduct nodes y ∧
      cardinal (appendNodes nodes y) (Fin.last n) t =
        nodeProduct nodes t / nodeProduct nodes y ∧
      lebesgue (appendNodes nodes y) t ≥
        |nodeProduct nodes t| / |nodeProduct nodes y|

/-- Projection algebra, Newton increments, and their point-evaluation norms. -/
def claim36107 : Prop :=
  ∀ (x : ℕ → ℝ), Function.Injective x →
    (∀ (m n : ℕ), m ≤ n →
      (∀ (Q : Polynomial ℝ), Q.natDegree < m →
        ∀ t : ℝ, prefixInterpolant x m (fun u => Q.eval u) t = Q.eval t) ∧
      (∀ (f : ℝ → ℝ) (i : Fin m),
        prefixInterpolant x m f (x i.1) = prefixInterpolant x n f (x i.1)) ∧
      (∀ (f : ℝ → ℝ) (t : ℝ),
        prefixInterpolant x m (fun u => prefixInterpolant x n f u) t =
          prefixInterpolant x m f t) ∧
      (∀ (f : ℝ → ℝ) (t : ℝ),
        prefixInterpolant x n (fun u => prefixInterpolant x m f u) t =
          prefixInterpolant x m f t)) ∧
    (∀ (f : ℝ → ℝ) (t : ℝ), prefixInterpolant x 0 f t = 0) ∧
    (∀ (n : ℕ) (f : ℝ → ℝ) (t : ℝ),
      interpolationIncrement x n
          (fun u => interpolationIncrement x n f u) t =
        interpolationIncrement x n f t) ∧
    (∀ (m n : ℕ), m ≠ n → ∀ (f : ℝ → ℝ) (t : ℝ),
      interpolationIncrement x m
          (fun u => interpolationIncrement x n f u) t = 0) ∧
    (∀ (n : ℕ) (f : ℝ → ℝ) (t : ℝ),
      prefixInterpolant x n f t =
        ∑ j ∈ Finset.range n, interpolationIncrement x j f t) ∧
    (∀ (n : ℕ) (t : ℝ),
      pointEvaluationNormOfIncrement x n t =
        normalization (prefixNodes x (n + 1)) *
          |nodeProduct (prefixNodes x n) t|
    )

/-- Reciprocal-derivative weights, their insertion recursion, and signed Cauchy form. -/
def claim36108 : Prop :=
  ∀ (n : ℕ) (nodes : Fin n → ℝ) (y : ℝ),
    1 ≤ n →
    Function.Injective nodes →
    (∀ i : Fin n, y ≠ nodes i) →
      (∀ i : Fin n, 0 < qWeight nodes i) ∧
      (∑ i : Fin n, qWeight nodes i = 1) ∧
      normalization (appendNodes nodes y) =
        (1 + lebesgue nodes y) / |nodeProduct nodes y| ∧
      qWeight (appendNodes nodes y) (Fin.last n) =
        1 / (1 + lebesgue nodes y) ∧
      (∀ i : Fin n,
        qWeight (appendNodes nodes y) (Fin.castSucc i) =
          |cardinal nodes i y| / (1 + lebesgue nodes y)) ∧
      ((∀ i j : Fin n, i.1 < j.1 → nodes i < nodes j) →
        ∀ t : ℝ, (∀ i : Fin n, t ≠ nodes i) →
          lebesgue nodes t =
            (∑ i : Fin n, qWeight nodes i / |t - nodes i|) /
              |∑ i : Fin n,
                signedEpsilon n i * qWeight nodes i / (t - nodes i)|)

/-- Cardinal-product, representing-measure, and persistence identities. -/
def claim36112 : Prop :=
  ∀ (n : ℕ) (nodes : Fin n → ℝ) (y t : ℝ),
    1 ≤ n →
    Function.Injective nodes →
    (∀ i : Fin n, y ≠ nodes i) →
      (∏ i : Fin n, |cardinal nodes i y| =
        |nodeProduct nodes y| ^ (n - 1) / (vandermonde nodes) ^ 2) ∧
      (∀ i : Fin n,
        cardinal (appendNodes nodes y) (Fin.castSucc i) t - cardinal nodes i t =
          -(nodeProduct nodes t / nodeProduct nodes y) * cardinal nodes i y) ∧
      cardinal (appendNodes nodes y) (Fin.last n) t =
        nodeProduct nodes t / nodeProduct nodes y ∧
      lebesgue nodes t + lebesgue (appendNodes nodes y) t ≥
        |nodeProduct nodes t / nodeProduct nodes y| * (1 + lebesgue nodes y) ∧
      |nodeProduct nodes t / nodeProduct nodes y| * (1 + lebesgue nodes y) =
        normalization (appendNodes nodes y) * |nodeProduct nodes t|

/-- The explicit reflected two-point nested fiber and its uniform bounds. -/
def reflectedFiberNodes (a b : ℝ) (k : ℕ) : ℝ :=
  let c := (a + b) / 2
  let d := (b - a) / 2
  let alpha := (1 / 2 : ℝ) * min (d ^ 2) ((1 - |c|) ^ 2 - d ^ 2)
  let theta := (1 / 4 : ℝ)
  let r := alpha * theta ^ (k / 2)
  let s := Real.sqrt (d ^ 2 + r)
  if Even k then c + s else c - s

/-- Reflected two-point fiber protection with the stated constants. -/
def claim36123 : Prop :=
  ∀ (a b : ℝ), a < b → -1 < a → a < 1 → -1 < b → b < 1 →
    let c := (a + b) / 2
    let d := (b - a) / 2
    let alpha := (1 / 2 : ℝ) * min (d ^ 2) ((1 - |c|) ^ 2 - d ^ 2)
    let theta := (1 / 4 : ℝ)
    let r (j : ℕ) := alpha * theta ^ (j - 1)
    let s (j : ℕ) := Real.sqrt (d ^ 2 + r j)
    let nodes := reflectedFiberNodes a b
    (0 < alpha ∧ theta = 1 / 4 ∧
      (∀ j : ℕ, 1 ≤ j →
        nodes (2 * j - 2) = c + s j ∧ nodes (2 * j - 1) = c - s j ∧
        nodes (2 * j - 1) < a ∧ b < nodes (2 * j - 2)) ∧
      (∀ k : ℕ, -1 < nodes k ∧ nodes k < 1) ∧
      (Function.Injective nodes) ∧
      (∀ M : ℕ, 1 ≤ M →
        prefixLebesgue nodes (2 * M) a = prefixLebesgue nodes (2 * M) b ∧
        prefixLebesgue nodes (2 * M) a < 3 ∧
        prefixLebesgue nodes (2 * M) b < 3 ∧
        prefixLebesgue nodes (2 * M - 1) b < 7 / 2 ∧
        prefixLebesgue nodes (2 * M - 1) a < 19 / 2) ∧
      (∀ n : ℕ,
        max (prefixLebesgue nodes n a) (prefixLebesgue nodes n b) ≤ 19 / 2))

end MathlibPlus.Open.ResearchFormalization
