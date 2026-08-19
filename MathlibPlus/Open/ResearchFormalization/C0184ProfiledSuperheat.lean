import Mathlib
import MathlibPlus.Open.ResearchFormalization.C0184GrowingEulerMoments

open Filter MeasureTheory Set Asymptotics
open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.C0184ProfiledSuperheat

noncomputable section

/-- The three Gaussian carriers fixed by C-0180. -/
def hProfile (x : ℝ) : ℝ :=
  x ^ 2 * (2 * Real.pi * x ^ 2 - 3) * Real.exp (-Real.pi * x ^ 2)

def gProfile (x : ℝ) : ℝ := Real.exp (-Real.pi * x ^ 2)

def r0Profile (x : ℝ) : ℝ :=
  (1 - 2 * Real.pi * x ^ 2) * Real.exp (-Real.pi * x ^ 2)

/-- The formal operator exponential `exp (-alpha * mathcalZ^k)`, using
C-0180's canonical shifted-Euler operator. -/
def superheatOperator (α : ℝ) (k : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => ∑' n : ℕ,
    ((-α) ^ n / (Nat.factorial n : ℝ)) *
      ((C0184.mathcalZ^[k * n]) f) x

/-- The baseline and the two independent C-0180 carriers. -/
def baselineCarrier (α : ℝ) (k : ℕ) : ℝ → ℝ :=
  superheatOperator α k hProfile

def carrierScale (α : ℝ) (k : ℕ) : ℝ :=
  Real.exp (α * (-1 / 4 : ℝ) ^ k)

def integralCarrier (α : ℝ) (k : ℕ) : ℝ → ℝ :=
  carrierScale α k • superheatOperator α k gProfile

def centerCarrier (α : ℝ) (k : ℕ) : ℝ → ℝ :=
  carrierScale α k • superheatOperator α k r0Profile

/-- Iteration of the canonical Euler differentiation used in the cutoff
estimate. -/
def eulerIterate (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (C0184.eulerD^[n]) f

noncomputable def realSupNorm (f : ℝ → ℝ) : ℝ :=
  sSup (Set.range (fun x : ℝ => |f x|))

/-- A fixed C-0180 logarithmic Gevrey cutoff of the required order. -/
def logGevreyBaseCutoff (k : ℕ) (θ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ ∧
    (∀ t : ℝ, t ≤ 1 / 2 → θ t = 1) ∧
    (∀ t : ℝ, 1 ≤ t → θ t = 0) ∧
    (∀ n : ℕ, iteratedDeriv n θ 1 = 0) ∧
    (∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ n : ℕ, ∀ t : ℝ,
        ‖iteratedDeriv n θ t‖ ≤
          C * A ^ n *
            Real.rpow (Nat.factorial n : ℝ)
              (1 + 1 / (2 * (k : ℝ))))

/-- The induced even cutoff from the logarithmic coordinate in C-0180. -/
def logGevreyCutoff (θ : ℝ → ℝ) (lam : ℝ) : ℝ → ℝ :=
  fun x => if |x| ≤ 1 then 1 else θ (Real.log |x| / Real.log lam)

/-- The concrete cutoff properties retained by the profiled construction. -/
def inducedCutoffProperties
    (k : ℕ) (θ : ℝ → ℝ) (lam : ℝ) : Prop :=
  1 < lam ∧
    (∀ x : ℝ, |x| ≤ Real.sqrt lam →
      logGevreyCutoff θ lam x = 1) ∧
    Function.support (logGevreyCutoff θ lam) ⊆ Set.Icc (-lam) lam ∧
    (∀ n : ℕ,
      iteratedDeriv n (logGevreyCutoff θ lam) (-lam) = 0 ∧
        iteratedDeriv n (logGevreyCutoff θ lam) lam = 0) ∧
    (∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ,
        realSupNorm (eulerIterate n (logGevreyCutoff θ lam)) ≤
          C ^ (n + 1) *
            Real.rpow (n + 1 : ℝ)
              ((1 + 1 / (2 * (k : ℝ))) * (n : ℝ)) *
            Real.rpow (Real.log lam) (-(n : ℝ)))

/-- The profiled carrier `P_L(mathcalZ/L^(1/k)) H_(alpha,k)` with real
logarithmic scale `L`, using the canonical C-0184 profile expansion. -/
def profiledCarrier
    (k : ℕ) (α : ℝ) (d : ℝ → ℕ) (a : ℝ → ℕ → ℝ) (L : ℝ) : ℝ → ℝ :=
  C0184.growingProfileCarrier k (baselineCarrier α k) d a L

/-- Claim 2733: the real-parameter shifted-Euler profile retains the
explicit C-0180 center, normalized-integral, and cutoff carriers. -/
def profiledSuperheatCarrier_claim2733
    (k : ℕ) (α : ℝ) (d : ℝ → ℕ) (a : ℝ → ℕ → ℝ) : Prop :=
  1 ≤ k ∧ 0 < α ∧
    ∃ θ : ℝ → ℝ,
      logGevreyBaseCutoff k θ ∧
        ∀ lam : ℝ, 1 < lam →
          inducedCutoffProperties k θ lam ∧
            C0184.centerMoment (profiledCarrier k α d a (Real.log lam)) =
              C0184.centerMoment (baselineCarrier α k) ∧
            C0184.normalizedIntegral (profiledCarrier k α d a (Real.log lam)) =
              C0184.normalizedIntegral (baselineCarrier α k) ∧
            ∃ b : ℝ,
              C0184.normalizedIntegral
                  ((logGevreyCutoff θ lam) *
                    (profiledCarrier k α d a (Real.log lam) +
                      (lam ^ (-2 : ℤ)) • centerCarrier α k - b • integralCarrier α k)) =
                0

end

end MathlibPlus.Open.ResearchFormalization.C0184ProfiledSuperheat
