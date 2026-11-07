import NLS.KdV.KdVPhysicalWeakSolution
import NLS.KdV.KdVClassicalApproximation

/-! Smooth physical approximation implies both the original conservation
solution concept and the independent integrated weak PDE. The converse
for arbitrary weak L² trajectories is deliberately not included. -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.KdV

theorem IsKdVSolutionByClassicalApproximation.continuous
    {u : ℝ → RealPeriodOneHillPotential} (hu : IsKdVSolutionByClassicalApproximation u) :
    Continuous u := by
  obtain ⟨v,hv,hlim⟩ := hu
  apply continuous_iff_continuousAt.mpr
  intro t
  let T := |t|+1
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hcont := (hlim T hT).continuousOn (Frequently.of_forall
    (fun N => (hv N).continuous.continuousOn (s := Icc (-T) T)))
  have hlow : -T < t := by dsimp [T]; linarith [neg_abs_le t]
  have hhigh : t < T := by dsimp [T]; linarith [le_abs_self t]
  exact (hcont t ⟨hlow.le,hhigh.le⟩).continuousAt (Icc_mem_nhds hlow hhigh)

/-- Locally uniform physical L² approximation by genuine smooth real
periodic KdV trajectories, with the literal original Fourier coefficients. -/
def IsKdVSolutionBySmoothPhysicalApproximation (u : ℝ → RealPeriodOneHillPotential) : Prop :=
  ∃ (v : ℕ → ℝ → RealPeriodOneHillPotential)
    (Q : ℕ → ℝ → C(AddCircle (2 : ℝ),ℂ)),
    (∀ N, IsSmoothPhysicalKdVTrajectory (Q N)) ∧
    (∀ N t, SpectralWeight.one.toCoeff (v N t).val = Fourier.continuousFourierCLM (Q N t)) ∧
    ∀ T : ℝ, 0 ≤ T → TendstoUniformlyOn v u atTop (Icc (-T) T)

theorem IsKdVSolutionBySmoothPhysicalApproximation.byClassicalApproximation
    {u : ℝ → RealPeriodOneHillPotential} (hu : IsKdVSolutionBySmoothPhysicalApproximation u) :
    IsKdVSolutionByClassicalApproximation u := by
  obtain ⟨v,Q,hQ,hsource,hlim⟩ := hu
  exact ⟨v,fun N => (hQ N).toClassicalKdVTrajectory (v N) (hsource N),hlim⟩

/-- Smooth approximation solutions satisfy the independently defined weak
PDE; no action conservation is assumed in deriving this implication. -/
theorem IsKdVSolutionBySmoothPhysicalApproximation.fourierWeak
    {u : ℝ → RealPeriodOneHillPotential} (hu : IsKdVSolutionBySmoothPhysicalApproximation u) :
    IsFourierWeakKdVTrajectory u := by
  have hc := hu.byClassicalApproximation.continuous
  obtain ⟨v,Q,hQ,hsource,hlim⟩ := hu
  exact isFourierWeakKdVTrajectory_of_locallyUniformLimit v u
    (fun N => isFourierWeakKdVTrajectory_of_smooth_physical (v N) (Q N) (hsource N) (hQ N)) hc hlim

end NLS.KdV
