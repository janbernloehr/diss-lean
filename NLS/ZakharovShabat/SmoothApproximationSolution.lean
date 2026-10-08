import NLS.ZakharovShabat.SmoothNLSDataDensity

/-! # Solutions defined by arbitrary smooth approximation

The dissertation's solution notion requires continuity, the prescribed value
at zero, and pointwise convergence for every convergent sequence of smooth
initial data. Smooth density makes this condition determine a unique curve
on its time domain. The classical solution family here is constructed.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The all-smooth-sequence solution condition for a fixed classical evolution.
The domain contains zero; equality and uniqueness concern only this domain. -/
structure IsSmoothApproximationSolutionOn
    (S : SmoothNLSData → ℝ → realTypeSourceSubmodule p)
    (J : Set ℝ) (φ : realTypeSourceSubmodule p)
    (γ : ℝ → realTypeSourceSubmodule p) : Prop where
  zero_mem : 0 ∈ J
  continuous : ContinuousOn γ J
  initial : γ 0 = φ
  approximation : ∀ f : ℕ → SmoothNLSData,
    Tendsto (fun j => (f j).source p) atTop (𝓝 φ) →
      ∀ time ∈ J, Tendsto (fun j => S (f j) time) atTop (𝓝 (γ time))

/-- Ordinary NLS in the sense of arbitrary smooth initial-data approximation. -/
abbrev IsOrdinaryNLSSolutionOn :=
  IsSmoothApproximationSolutionOn (fun f : SmoothNLSData => f.ordinarySource p)

/-- Renormalized NLS in the dissertation's arbitrary smooth approximation sense. -/
abbrev IsRenormalizedNLSSolutionOn :=
  IsSmoothApproximationSolutionOn (fun f : SmoothNLSData => f.renormalizedSource p)

/-- Smooth density makes any two approximation solutions agree wherever both are defined. -/
theorem IsSmoothApproximationSolutionOn.eqOn_inter
    {S : SmoothNLSData → ℝ → realTypeSourceSubmodule p}
    {J K : Set ℝ} {φ : realTypeSourceSubmodule p} {γ η : ℝ → realTypeSourceSubmodule p}
    (hγ : IsSmoothApproximationSolutionOn S J φ γ)
    (hη : IsSmoothApproximationSolutionOn S K φ η) (hp : p ≠ ⊤) (hp1 : 1 < p) :
    EqOn γ η (J ∩ K) := by
  obtain ⟨f,hf⟩ := exists_smoothNLSData_sequence hp hp1 φ
  intro time htime
  exact tendsto_nhds_unique (hγ.approximation f hf time htime.1)
    (hη.approximation f hf time htime.2)

/-- Restricting a solution to a smaller time domain containing zero preserves the definition. -/
theorem IsSmoothApproximationSolutionOn.restrict
    {S : SmoothNLSData → ℝ → realTypeSourceSubmodule p}
    {J K : Set ℝ} {φ : realTypeSourceSubmodule p} {γ : ℝ → realTypeSourceSubmodule p}
    (hγ : IsSmoothApproximationSolutionOn S J φ γ) (hK : K ⊆ J) (hzero : 0 ∈ K) :
    IsSmoothApproximationSolutionOn S K φ γ :=
  ⟨hzero,hγ.continuous.mono hK,hγ.initial,fun f hf time ht => hγ.approximation f hf time (hK ht)⟩

end NLS.ZakharovShabat
