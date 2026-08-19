import MathlibPlus.Open.ResearchFormalizationBatch_01a0032b.Weyl

namespace MathlibPlus.Open.ResearchFormalization.K0023Claim7575

noncomputable section

open MathlibPlus.Open.Batch_01a0032b

/-- The exact real even super-exponential source condition. -/
def sourceCondition7575 (Φ : ℝ → ℝ) : Prop :=
  superExponentialRealSource Φ

/-- The source transform `Xi`. -/
def xi7575 (Φ : ℝ → ℝ) (z : ℂ) : ℂ :=
  sourceTransform Φ z

/-- The correlation `C_y(Σ)`. -/
def correlation7575 (Φ : ℝ → ℝ) (y : ℝ) (sigma : ℂ) : ℂ :=
  sourceCorrelation Φ y sigma

/-- The coordinate Weyl kernel `K_ω(a,b)`. -/
def coordinateKernel7575 (Φ : ℝ → ℝ) (ω a b : ℝ) : ℝ :=
  coordinateWeylKernel Φ ω a b

/-- The shifted de Branges function `E_ω(z)=Xi(z+iω)`. -/
def shiftedXi7575 (Φ : ℝ → ℝ) (ω : ℝ) (z : ℂ) : ℂ :=
  xi7575 Φ (z + (ω : ℂ) * Complex.I)

/-- The de Branges kernel integral with its removable diagonal convention. -/
def deBrangesKernel7575 (Φ : ℝ → ℝ) (ω : ℝ) (w z : ℂ) : ℂ :=
  deBrangesKernelIntegral Φ ω w z

/-- The bilateral Fourier--Laplace Weyl compression of the coordinate kernel. -/
def weylCompression7575 (Φ : ℝ → ℝ) (ω : ℝ) (w z : ℂ) : ℂ :=
  weylCompressionIntegral Φ ω w z

end

end MathlibPlus.Open.ResearchFormalization.K0023Claim7575
