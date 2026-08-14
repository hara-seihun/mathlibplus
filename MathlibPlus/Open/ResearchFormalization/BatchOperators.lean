import Mathlib

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.ResearchFormalization
def weaklyNull {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (u : ℕ → E) : Prop :=
  ∀ φ : E →L[𝕜] 𝕜,
    Filter.Tendsto (fun n => φ (u n)) Filter.atTop (nhds 0)

def compactLinearMap {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] (T : E →L[𝕜] F) : Prop :=
  IsCompact (closure (T '' Metric.closedBall (0 : E) 1))

def claim3922 {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    (K : Set (E →L[𝕜] F)) (u : ℕ → E) (T : ℕ → E →L[𝕜] F) : Prop :=
  IsCompact K →
    (∀ S ∈ K, compactLinearMap S) →
    (∃ C : ℝ, ∀ n, ‖u n‖ ≤ C) →
    weaklyNull (𝕜 := 𝕜) u →
    (∀ n, T n ∈ K) →
    Filter.Tendsto (fun n => T n (u n)) Filter.atTop (nhds 0)

def claim3923 {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    (K : Set (E →L[𝕜] F)) (u : ℕ → E) (T : ℕ → E →L[𝕜] F) : Prop :=
  IsCompact K →
    (∀ S ∈ K, compactLinearMap S) →
    (∃ C : ℝ, ∀ n, ‖u n‖ ≤ C) →
    weaklyNull (𝕜 := 𝕜) u →
    (∀ n, T n ∈ K) →
    (let σ := fun n =>
       sSup {r : ℝ | ∃ S ∈ K, r = ‖S (u n)‖}
     Filter.Tendsto σ Filter.atTop (nhds 0) ∧
       ∀ S : ℕ → E →L[𝕜] F, (∀ n, S n ∈ K) →
         Filter.Tendsto (fun n => S n (u n)) Filter.atTop (nhds 0))

def claim3928 {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    (u : ℕ → E) (T : E →L[𝕜] F) : Prop :=
  weaklyNull (𝕜 := 𝕜) u → compactLinearMap T →
    Filter.Tendsto (fun j => T (u j)) Filter.atTop (nhds 0)

def claim3929 {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    (u : ℕ → E) (T : ℕ → E →L[𝕜] F) (η : ℝ) : Prop :=
  (∀ j, ‖u j‖ = 1) →
    (∀ j, compactLinearMap (T j)) →
    (Filter.Eventually (fun j => η ≤ ‖T j (u j)‖) Filter.atTop) →
    (∀ i : ℕ, ∀ r : ℝ, r < η →
      Filter.Eventually
        (fun j =>
          ‖(T j - T i) (u j)‖ ≤ ‖T j - T i‖ ∧
            r < ‖(T j - T i) (u j)‖) Filter.atTop)

def claim3930 {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    (u : ℕ → E) (T : ℕ → E →L[𝕜] F) : Prop :=
  (weaklyNull (𝕜 := 𝕜) u) →
    (∀ j, ‖u j‖ = 1) →
    (∀ j, compactLinearMap (T j)) →
    (let Λ := Filter.liminf (fun j => ‖T j (u j)‖) Filter.atTop
     Λ > 0 →
       ∀ r : ℝ, 0 < r → r < Λ →
         ∃ j : ℕ → ℕ, StrictMono j ∧
           ∀ ⦃k l : ℕ⦄, k < l → r ≤ ‖T (j l) - T (j k)‖)

def claim3932 {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    (T : ℕ → E →L[𝕜] F) (r : ℝ) : Prop :=
  (∀ i : ℕ, Filter.Eventually (fun j => r < ‖T j - T i‖) Filter.atTop) →
    ∃ j : ℕ → ℕ, StrictMono j ∧
      ∀ ⦃k l : ℕ⦄, k < l → r ≤ ‖T (j l) - T (j k)‖

def claim3933 {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    (K : Set (E →L[𝕜] F)) (u : ℕ → E) (T : ℕ → E →L[𝕜] F) : Prop :=
  TotallyBounded K →
    (∀ S ∈ K, compactLinearMap S) →
    weaklyNull (𝕜 := 𝕜) u →
    (∀ j, ‖u j‖ = 1) →
    (∀ j, T j ∈ K) →
    Filter.liminf (fun j => ‖T j (u j)‖) Filter.atTop = 0

def claim3935 {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    (u : ℕ → E) (K : E →L[𝕜] F) : Prop :=
  weaklyNull (𝕜 := 𝕜) u → compactLinearMap K →
    Filter.Tendsto (fun j => K (u j)) Filter.atTop (nhds 0)

def claim3942 {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F]
    [CompleteSpace E] [CompleteSpace F]
    (u : ℕ → E) (T : ℕ → E →L[𝕜] F) (j : ℕ → ℕ) (v : F) : Prop :=
  StrictMono j →
    Filter.Tendsto (fun k => T (j k) (u (j k))) Filter.atTop (nhds v) →
    v ≠ 0 →
      (let z : F := (‖v‖⁻¹ : 𝕜) • v
       ‖z‖ = 1 ∧
       (∀ k : ℕ,
         inner 𝕜 (u (j k)) ((ContinuousLinearMap.adjoint (T (j k))) z) =
           inner 𝕜 (T (j k) (u (j k))) z) ∧
       Filter.Tendsto
         (fun k => inner 𝕜 (u (j k)) ((ContinuousLinearMap.adjoint (T (j k))) z))
         Filter.atTop (nhds (‖v‖ : 𝕜)))

def claim3943 {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F]
    [CompleteSpace E] [CompleteSpace F]
    (u : ℕ → E) (T : ℕ → E →L[𝕜] F) : Prop :=
  weaklyNull (𝕜 := 𝕜) u →
    ∀ i : ℕ, ∀ z : F, ∀ j : ℕ → ℕ, StrictMono j →
      Filter.Tendsto
        (fun k => inner 𝕜 (u (j k)) ((ContinuousLinearMap.adjoint (T i)) z))
        Filter.atTop (nhds 0)

def claim3945 {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F]
    [CompleteSpace E] [CompleteSpace F]
    (u : ℕ → E) (T : ℕ → E →L[𝕜] F) : Prop :=
  (∀ j, ‖u j‖ ≤ 1) →
    weaklyNull (𝕜 := 𝕜) u →
    (let v := fun j => T j (u j)
     let Λ := Filter.liminf (fun j => ‖v j‖) Filter.atTop
     Λ > 0 →
       IsCompact (closure (Set.range v)) →
       (∃ z : F, ‖z‖ = 1 ∧
         ∃ j : ℕ → ℕ, StrictMono j ∧
           ∀ r : ℝ, 0 < r → r < Λ →
             ∃ k : ℕ → ℕ, StrictMono k ∧
               ∀ ⦃a b : ℕ⦄, a < b →
                 r ≤ ‖ContinuousLinearMap.adjoint (T (j (k a))) z -
                   ContinuousLinearMap.adjoint (T (j (k b))) z‖) ∧
       (∀ j₀ : ℕ → ℕ, ∀ w : F, StrictMono j₀ →
         Filter.Tendsto (fun k => v (j₀ k)) Filter.atTop (nhds w) →
           (‖w‖ ≥ Λ ∧
             (let z : F := (‖w‖⁻¹ : 𝕜) • w
              ‖z‖ = 1 ∧
                ∀ r : ℝ, 0 < r → r < ‖w‖ →
                  ∃ k : ℕ → ℕ, StrictMono k ∧
                    ∀ ⦃a b : ℕ⦄, a < b →
                      r ≤
                        ‖ContinuousLinearMap.adjoint (T (j₀ (k a))) z -
                          ContinuousLinearMap.adjoint (T (j₀ (k b))) z‖))))

def claim3953 {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    (u : ℕ → E) (T : ℕ → E →L[𝕜] F) : Prop :=
  weaklyNull (𝕜 := 𝕜) u →
    (∀ j, ‖u j‖ ≤ 1) →
    (let Λ := Filter.liminf (fun j => ‖T j (u j)‖) Filter.atTop
     Λ > 0 →
       ∃ ℓ : ℕ → F →L[𝕜] 𝕜,
         (∀ j, ‖ℓ j‖ = 1 ∧ ‖ℓ j (T j (u j))‖ = ‖T j (u j)‖) ∧
         ∀ r : ℝ, 0 < r → r < Λ →
           ∃ j : ℕ → ℕ, StrictMono j ∧
             ∀ ⦃k l : ℕ⦄, k < l →
               r ≤
                 ‖(ℓ (j l)).comp (T (j l)) -
                   (ℓ (j k)).comp (T (j k))‖)


end MathlibPlus.Open.ResearchFormalization
