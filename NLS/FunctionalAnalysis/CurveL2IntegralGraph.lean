import NLS.Fourier.CirclePrimitive
import NLS.FunctionalAnalysis.UnitComplexCurvePrimitive

/-! # Closed physical derivative graph with an L2 forcing and continuous correction -/
noncomputable section
open Set Complex Filter Topology MeasureTheory NLS.Fourier NLS.LinearVolterra
namespace NLS.FunctionalAnalysis

theorem unitCurve_regular_of_L2_integral_graph
    (f h : Curve ℂ) (g : CircleL2) (c d : ℂ)
    (hr : ∀ t : Icc (0:ℝ) 1, f t-f ⟨0,by norm_num⟩ =
      c*circlePrimitive t.val g+d*unitComplexCurvePrimitive h t) :
    AbsolutelyContinuousOnInterval (extend f) 0 1 ∧
      ∀ᵐ x ∂volume.restrict (Ioc (0:ℝ) 1),
        HasDerivAt (extend f) (c*circlePullback g x+d*extend h x) x := by
  have hi : IntervalIntegrable (circlePullback g) volume 0 1 :=
    (intervalIntegrable_circlePullback g).mono_set (by
      rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1),uIcc_of_le (by norm_num : (0:ℝ) ≤ 2)]
      exact Icc_subset_Icc le_rfl (by norm_num))
  have hG := absolutelyContinuousOnInterval_integral hi (c := (0:ℝ)) (by simp)
  have hG' := absolutelyContinuousOnInterval_clm hG
    ((c • ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ)
  have hH' := absolutelyContinuousOnInterval_clm (absolutelyContinuousOnInterval_unitComplexCurvePrimitive h)
    ((d • ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ)
  have hF : AbsolutelyContinuousOnInterval
      (fun x => f ⟨0,by norm_num⟩+(c*circlePrimitive x g+d*extend (unitComplexCurvePrimitive h) x)) 0 1 :=
    absolutelyContinuousOnInterval_const_add (hG'.add hH') _
  have hEq (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :
      extend f x = f ⟨0,by norm_num⟩+
        (c*circlePrimitive x g+d*extend (unitComplexCurvePrimitive h) x) := by
    rw [extend_coe f ⟨x,hx⟩,extend_coe _ ⟨x,hx⟩]
    linear_combination hr ⟨x,hx⟩
  refine ⟨absolutelyContinuousOnInterval_congr hF (fun x hx => (hEq x (by
    simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hx)).symm),?_⟩
  have hgd := ae_restrict_of_ae (s := Ioc (0:ℝ) 1) hi.ae_hasDerivAt_integral
  filter_upwards [hgd,ae_hasDerivAt_unitComplexCurvePrimitive h,
    ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae (show ∀ᵐ x : ℝ, x ≠ (1:ℝ) from by simp [ae_iff,measure_singleton])]
    with x hxG hxH hx hx1
  have hxi : x ∈ uIcc (0:ℝ) 1 := by
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact ⟨hx.1.le,hx.2⟩
  have hd := (((hxG hxi 0 (by simp)).const_mul c).add (hxH.const_mul d)).const_add
    (f ⟨0,by norm_num⟩)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hx.1 (lt_of_le_of_ne hx.2 hx1)] with y hy
  exact hEq y ⟨hy.1.le,hy.2.le⟩

end NLS.FunctionalAnalysis
