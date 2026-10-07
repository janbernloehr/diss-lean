import NLS.ZakharovShabat.SmoothClassicalNLSAgreementExponent

/-! # Arbitrary classical approximations in the original source norms

Convergence of the actual smooth initial Fourier sources implies uniform
compact-time convergence of the classical source curves. The higher-exponent
renormalized result retains admissibility of the limiting compact-time path.
-/
noncomputable section
open Set Filter Topology NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceAbelianMomentAtlas
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W P V B X : Set (CoeffPair p)}
variable {s t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Every classical ordinary approximation converges uniformly in the
original p-source norm in the global exponent range, from initial convergence alone. -/
theorem tendstoUniformlyOn_classicalNLSSource_of_smoothInitial
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 V B X t)
    (hp2 : p ≤ 2) {ι : Type*} {l : Filter ι}
    (u : ι → ℝ → C(AddCircle (2 : ℝ), ℂ)) (hu : ∀ j, IsClassicalNLSTrajectory (u j))
    (φ : realTypeSourceSubmodule p)
    (hinit : Tendsto (fun j => smoothPeriodOneSourceAt p (u j 0)
      ((hu j).spatial_smooth 0) ((hu j).periodic 0)) l (𝓝 φ)) (T : ℝ) :
    TendstoUniformlyOn (fun j time => smoothPeriodOneSourceAt p (u j time)
      ((hu j).spatial_smooth time) ((hu j).periodic time))
      (A.hamiltonianOrdinarySourceFlow D hp2 φ) l (Icc (-T) T) := by
  let F := A.hamiltonianOrdinarySourceTrajectoryOn hs hP hr D hp2 T
  have hlim := A.tendsto_hamiltonianOrdinarySourceTrajectoryOn hs hP hr D hp2 T φ _ hinit
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(Metric.tendsto_nhds.mp hlim) ε hε] with j hj
  intro time htime
  rw [A.classicalNLS_source_eq_flow hs.toSourcePsiIsolatingComplexExtension D hp2 (u j) (hu j) time]
  have hbound := ContinuousMap.dist_apply_le_dist (f := F φ)
    (g := F (smoothPeriodOneSourceAt p (u j 0) ((hu j).spatial_smooth 0) ((hu j).periodic 0))) ⟨time,htime⟩
  exact hbound.trans_lt (by simpa only [dist_comm] using! hj)

/-- Every classical renormalized approximation converges uniformly in the
original p-source norm in the global exponent range, from initial convergence alone. -/
theorem tendstoUniformlyOn_classicalRenormalizedNLSSource_of_smoothInitial
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 V B X t)
    (hp2 : p ≤ 2) {ι : Type*} {l : Filter ι}
    (u : ι → ℝ → C(AddCircle (2 : ℝ), ℂ)) (hu : ∀ j, IsClassicalRenormalizedNLSTrajectory (classicalNLSMass (u j 0)) (u j))
    (φ : realTypeSourceSubmodule p)
    (hinit : Tendsto (fun j => smoothPeriodOneSourceAt p (u j 0)
      ((hu j).spatial_smooth 0) ((hu j).periodic 0)) l (𝓝 φ)) (T : ℝ) :
    TendstoUniformlyOn (fun j time => smoothPeriodOneSourceAt p (u j time)
      ((hu j).spatial_smooth time) ((hu j).periodic time))
      (A.hamiltonianRenormalizedSourceFlow D hp2 φ) l (Icc (-T) T) := by
  let F := A.hamiltonianRenormalizedSourceTrajectoryOn hs hP hr D hp2 T
  have hlim := A.tendsto_hamiltonianRenormalizedSourceTrajectoryOn hs hP hr D hp2 T φ _ hinit
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(Metric.tendsto_nhds.mp hlim) ε hε] with j hj
  intro time htime
  rw [A.classicalRenormalizedNLS_source_eq_flow hs.toSourcePsiIsolatingComplexExtension D hp2 (u j) (hu j) time]
  have hbound := ContinuousMap.dist_apply_le_dist (f := F φ)
    (g := F (smoothPeriodOneSourceAt p (u j 0) ((hu j).spatial_smooth 0) ((hu j).periodic 0))) ⟨time,htime⟩
  exact hbound.trans_lt (by simpa only [dist_comm] using! hj)

/-- In the higher-exponent local regime, arbitrary smooth classical
approximations converge on each admissible compact interval of the rough limit.
Each approximant uses its own physical mass; no finite-gap condition is imposed. -/
theorem tendstoUniformlyOn_classicalRenormalizedImageSource_of_smoothInitial
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 V B X t)
    (h2p : 2 ≤ p) {ι : Type*} {l : Filter ι}
    (u : ι → ℝ → C(AddCircle (2 : ℝ), ℂ))
    (hu : ∀ j, IsClassicalRenormalizedNLSTrajectory (classicalNLSMass (u j 0)) (u j))
    (φ : realTypeSourceSubmodule p)
    (hinit : Tendsto (fun j => smoothPeriodOneSourceAt p (u j 0)
      ((hu j).spatial_smooth 0) ((hu j).periodic 0)) l (𝓝 φ)) (T : ℝ)
    (hφ : φ ∈ A.renormalizedTrajectoryDomain t T) :
    TendstoUniformlyOn (fun j time => smoothPeriodOneSourceAt p (u j time)
      ((hu j).spatial_smooth time) ((hu j).periodic time))
      (A.hamiltonianRenormalizedImageFlow D φ) l (Icc (-T) T) := by
  let F := A.hamiltonianRenormalizedImageTrajectoryOn D T
  have hlim := (A.analytic_hamiltonianRenormalizedImageTrajectoryOn hs hP hr D T φ hφ).continuousAt.tendsto.comp hinit
  have hvalid (j : ι) : smoothPeriodOneSourceAt p (u j 0)
      ((hu j).spatial_smooth 0) ((hu j).periodic 0) ∈ A.renormalizedTrajectoryDomain t T := by
    intro time
    simpa only [neg_neg] using! A.smoothPeriodOneSourceAt_mem_renormalizedImageDomain
      hs.toSourcePsiIsolatingComplexExtension D h2p (u j 0)
      ((hu j).spatial_smooth 0) ((hu j).periodic 0) (-time.val)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(Metric.tendsto_nhds.mp hlim) ε hε] with j hj
  intro time htime
  rw [A.classicalRenormalizedNLS_source_eq_imageFlow hs.toSourcePsiIsolatingComplexExtension D (u j) (hu j) time]
  have hbound := ContinuousMap.dist_apply_le_dist (f := F φ)
    (g := F (smoothPeriodOneSourceAt p (u j 0) ((hu j).spatial_smooth 0) ((hu j).periodic 0))) ⟨time,htime⟩
  change dist (A.hamiltonianRenormalizedImageTrajectoryOn D T φ ⟨time,htime⟩)
    (A.hamiltonianRenormalizedImageTrajectoryOn D T
      (smoothPeriodOneSourceAt p (u j 0) ((hu j).spatial_smooth 0) ((hu j).periodic 0)) ⟨time,htime⟩) ≤ _ at hbound
  rw [A.hamiltonianRenormalizedImageTrajectoryOn_apply hs hP hr D T φ hφ,
    A.hamiltonianRenormalizedImageTrajectoryOn_apply hs hP hr D T _ (hvalid j)] at hbound
  exact hbound.trans_lt (by simpa only [dist_comm] using! hj)

end NLS.ZakharovShabat.SourceAbelianMomentAtlas
