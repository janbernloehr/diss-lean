import NLS.SequenceSpaces.RealQuadraticActionOpening

/-! Dividing an invariant scalar by a quadratic action preserves real
fiber invariance even at closed actions, provided the normalized factor
is continuous. Simultaneous real opening proves the closed case. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.Coeff

theorem eq_on_real_action_fibers_of_normalized_invariant
    (U : Set (Coeff 2 × Coeff 2)) (hU : IsOpen U) (j : ℤ)
    (f G : (Coeff 2 × Coeff 2) → ℂ) (hf : ContinuousOn f U)
    (hG : ∀ z∈U, ∀ w∈U, z∈realPairLocus 2 → w∈realPairLocus 2 →
      quadraticActionsExponent (q := 1) w=quadraticActionsExponent z → G w=G z)
    (hfac : ∀ z∈U, z∈realPairLocus 2 → quadraticActionsExponent (q := 1) z j*f z=G z)
    (z : Coeff 2 × Coeff 2) (hz : z∈U) (hzr : z∈realPairLocus 2)
    (w : Coeff 2 × Coeff 2) (hw : w∈U) (hwr : w∈realPairLocus 2)
    (ha : quadraticActionsExponent (q := 1) w=quadraticActionsExponent z) : f w=f z := by
  have hopen (x : Coeff 2 × Coeff 2) (hx : x∈U) (hxr : x∈realPairLocus 2)
      (y : Coeff 2 × Coeff 2) (hy : y∈U) (hyr : y∈realPairLocus 2)
      (hxy : quadraticActionsExponent (q := 1) y=quadraticActionsExponent x)
      (hne : quadraticActionsExponent (q := 1) x j≠0) : f y=f x := by
    apply mul_left_cancel₀ hne
    calc
      _=quadraticActionsExponent (q := 1) y j*f y := by rw [hxy]
      _=G y := hfac y hy hyr
      _=G x := hG x hx y hy hxr hyr hxy
      _=_ := (hfac x hx hxr).symm
  by_cases h0 : quadraticActionsExponent (q := 1) z j=0
  · have hzt : Tendsto (realCoordinateOpening j z) (𝓝 (0 : ℝ)) (𝓝 z) := by
      simpa only [realCoordinateOpening_zero] using (continuous_realCoordinateOpening j z).tendsto 0
    have hwt : Tendsto (realCoordinateOpening j w) (𝓝 (0 : ℝ)) (𝓝 w) := by
      simpa only [realCoordinateOpening_zero] using (continuous_realCoordinateOpening j w).tendsto 0
    have hnear : ∀ᶠ t : ℝ in 𝓝 0, realCoordinateOpening j z t∈U ∧ realCoordinateOpening j w t∈U :=
      (hzt.eventually (hU.mem_nhds hz)).and (hwt.eventually (hU.mem_nhds hw))
    have he : (fun t : ℝ => f (realCoordinateOpening j w t)) =ᶠ[𝓝[≠] (0 : ℝ)]
        (fun t => f (realCoordinateOpening j z t)) := by
      filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with t ht htn
      have ht0 : t≠0 := by simpa only [mem_compl_iff,mem_singleton_iff] using htn
      exact hopen (realCoordinateOpening j z t) ht.1 (realCoordinateOpening_real j z hzr t)
        (realCoordinateOpening j w t) ht.2 (realCoordinateOpening_real j w hwr t)
        (realCoordinateOpening_actions_eq j z w hzr hwr ha h0 t)
        (realCoordinateOpening_action_ne_zero j z hzr h0 t ht0)
    have hflw : Tendsto (fun t => f (realCoordinateOpening j w t)) (𝓝[≠] (0 : ℝ)) (𝓝 (f w)) := ((hf.continuousAt (hU.mem_nhds hw)).tendsto.comp hwt).mono_left nhdsWithin_le_nhds
    have hflz : Tendsto (fun t => f (realCoordinateOpening j z t)) (𝓝[≠] (0 : ℝ)) (𝓝 (f z)) := ((hf.continuousAt (hU.mem_nhds hz)).tendsto.comp hzt).mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique (hflw.congr' he) hflz
  · exact hopen z hz hzr w hw hwr ha h0

end NLS.Coeff
