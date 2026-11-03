import NLS.MKdV.MiuraNativeCartesianCharts
import NLS.MKdV.MiuraSobolevNormalizedActionFlow
import Mathlib.Analysis.Calculus.Deriv.Add

/-! # Actual action-flow derivatives in every positive native Sobolev norm

The proved physical Cartesian inverse charts lift the finite-plane
rotation derivative to the full H^s source. This justifies native chain
rules for independent angle functionals on H¹, including closed actions.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem exists_hasDerivAt_miuraActionFlow_zero (s : ℕ) (hs : 1 ≤ s)
    (a : MiuraRealSobolevSource s) (n : ℕ) (hn : 1 ≤ n) :
    ∃ v : ScalarSobolev s, HasDerivAt (miuraActionFlow s a.val a.property n) v 0 := by
  have ha : ∀ j, a.val.val j = conj (a.val.val (-j)) := a.property
  obtain ⟨C⟩ := nonempty_miuraNativeCartesianChart s hs a
  let z := miuraSobolevNormalizedCartesianMap s a.val
  have hc := (C.inverse_analytic z (mem_ball_self C.radius_pos)).differentiableAt.hasFDerivAt.restrictScalars ℝ
  have ht := hasDerivAt_miuraCartesianRotation_zero n z
  have hc' : HasFDerivAt C.inverse ((fderiv ℂ C.inverse z).restrictScalars ℝ)
      (miuraCartesianRotation n 0 z) := by simpa only [miuraCartesianRotation_zero] using hc
  have hd := hc'.comp_hasDerivAt 0 ht
  have he : (fun t => C.inverse (miuraCartesianRotation n t z)) =ᶠ[𝓝 (0 : ℝ)]
      miuraActionFlow s a.val a.property n := by
    have hh : ∀ᶠ t in 𝓝 (0 : ℝ), miuraActionFlow s a.val a.property n t ∈ C.source := by
      have hzero := miuraActionFlow_zero s a.val ha n
      have hb : C.source ∈ 𝓝 (miuraActionFlow s a.val ha n 0) := by
        simpa only [hzero] using C.source_open.mem_nhds C.source_base
      exact (continuous_miuraActionFlow s a.val a.property n).continuousAt.preimage_mem_nhds hb
    filter_upwards [hh] with t ht
    rw [← miuraSobolevNormalizedCartesianMap_actionFlow s a.val a.property n hn t]
    exact C.left_inverse _ ht
  refine ⟨((fderiv ℂ C.inverse z).restrictScalars ℝ) (miuraCartesianActionVector n z), ?_⟩
  exact hd.congr_of_eventuallyEq he.symm

def miuraNativeActionVelocity (s : ℕ) (a : MiuraRealSobolevSource s) (n : ℕ) : ScalarSobolev s :=
  deriv (miuraActionFlow s a.val a.property n) 0

theorem hasDerivAt_miuraActionFlow_native_zero (s : ℕ) (hs : 1 ≤ s)
    (a : MiuraRealSobolevSource s) (n : ℕ) (hn : 1 ≤ n) :
    HasDerivAt (miuraActionFlow s a.val a.property n) (miuraNativeActionVelocity s a n) 0 := by
  obtain ⟨v,hv⟩ := exists_hasDerivAt_miuraActionFlow_zero s hs a n hn
  rw [miuraNativeActionVelocity,hv.deriv]
  exact hv

end NLS.MKdV
