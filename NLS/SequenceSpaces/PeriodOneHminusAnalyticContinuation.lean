import NLS.SequenceSpaces.PeriodOneHminusOneDensity
import Mathlib.Analysis.Analytic.Uniqueness

/-! # A native L2 analytic germ determines the whole complex rough ball

The inverse image of a rough ball under the literal L2 inclusion is convex,
so analytic continuation first reaches every L2 source in that rough ball.
Genuine dense-range continuity then reaches every complex rough source.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Filter Topology
namespace NLS

/-- A dense complex linear inclusion and one native analytic germ
identify functions on their whole common complex ball. -/
theorem eqOn_ball_of_dense_complexLinear_germ
    {E F Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (L : E →L[ℂ] F) (hL : DenseRange L) (η : ℝ) (hη : 0<η) (f g : F → Y)
    (hf : AnalyticOnNhd ℂ f (ball (0 : F) η))
    (hg : AnalyticOnNhd ℂ g (ball (0 : F) η))
    (he : (fun a : E => f (L a)) =ᶠ[𝓝 0] (fun a : E => g (L a))) :
    EqOn f g (ball (0 : F) η) := by
  let U : Set E := L ⁻¹' ball (0 : F) η
  have hconv : IsPreconnected U :=
    ((convex_ball (0 : F) η).linear_preimage (L.restrictScalars ℝ).toLinearMap).isPreconnected
  have h0 : (0 : E)∈U := by
    change L 0∈ball (0 : F) η
    rw [map_zero]
    exact mem_ball_self hη
  have hfa : AnalyticOnNhd ℂ (fun a : E => f (L a)) U :=
    fun a ha => (hf _ ha).comp (L.analyticAt a)
  have hga : AnalyticOnNhd ℂ (fun a : E => g (L a)) U :=
    fun a ha => (hg _ ha).comp (L.analyticAt a)
  have hEq : EqOn f g (ball (0 : F) η∩range L) := by
    rintro _ ⟨ha,a,rfl⟩
    exact hfa.eqOn_of_preconnected_of_eventuallyEq hga hconv h0 he ha
  exact hEq.of_subset_closure hf.continuousOn hg.continuousOn inter_subset_left
    (fun q hq => isOpen_ball.inter_closure ⟨hq,hL q⟩)

/-- Equality on ONE complex native L2 germ propagates throughout the
WHOLE common complex H-minus-one ball, with no L2 source-norm bound. -/
theorem eqOn_periodOneHminus_ball_of_L2_germ
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (η : ℝ) (hη : 0<η) (f g : PeriodOneHminusOne → Y)
    (hf : AnalyticOnNhd ℂ f (ball (0 : PeriodOneHminusOne) η))
    (hg : AnalyticOnNhd ℂ g (ball (0 : PeriodOneHminusOne) η))
    (he : (fun a : Coeff 2 => f (periodOneL2Inclusion a)) =ᶠ[𝓝 0]
      (fun a : Coeff 2 => g (periodOneL2Inclusion a))) :
    EqOn f g (ball (0 : PeriodOneHminusOne) η) := by
  exact eqOn_ball_of_dense_complexLinear_germ periodOneL2Inclusion
    denseRange_periodOneL2Inclusion η hη f g hf hg he

end NLS
