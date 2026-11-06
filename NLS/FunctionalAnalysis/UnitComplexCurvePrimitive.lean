import NLS.FunctionalAnalysis.ComplexVolterraOperator
import NLS.FunctionalAnalysis.ComplexAbsoluteContinuity

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.LinearVolterra
open scoped ENNReal ComplexConjugate Classical

namespace NLS.FunctionalAnalysis



/-- The bounded complex-linear zero-initial primitive of a continuous unit curve. -/
def unitComplexCurvePrimitive : Curve ℂ →L[ℂ] Curve ℂ :=
  volterra (ContinuousMap.const _ (ContinuousLinearMap.id ℂ ℂ))

theorem unitComplexCurvePrimitive_apply (g : Curve ℂ) (t : Icc (0 : ℝ) 1) :
    unitComplexCurvePrimitive g t=∫ x in (0 : ℝ)..t.val,NLS.LinearVolterra.extend g x := by
  rw [unitComplexCurvePrimitive,volterra_apply]
  rfl

private theorem primitive_extend_eq (g : Curve ℂ) (x : ℝ) (hx : x∈Icc (0 : ℝ) 1) :
    NLS.LinearVolterra.extend (unitComplexCurvePrimitive g) x=
      ∫ t in (0 : ℝ)..x,NLS.LinearVolterra.extend g t := by
  change unitComplexCurvePrimitive g (projIcc 0 1 (by norm_num) x)=_
  rw [projIcc_of_mem _ hx,unitComplexCurvePrimitive_apply]

theorem absolutelyContinuousOnInterval_unitComplexCurvePrimitive (g : Curve ℂ) :
    AbsolutelyContinuousOnInterval (NLS.LinearVolterra.extend (unitComplexCurvePrimitive g)) 0 1 := by
  have hi := absolutelyContinuousOnInterval_integral ((continuous_extend g).intervalIntegrable 0 1)
    (c := (0 : ℝ)) (by simp)
  apply absolutelyContinuousOnInterval_congr hi
  intro x hx
  exact (primitive_extend_eq g x (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ)≤1)] using hx)).symm

theorem ae_hasDerivAt_unitComplexCurvePrimitive (g : Curve ℂ) :
    ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (NLS.LinearVolterra.extend (unitComplexCurvePrimitive g)) (NLS.LinearVolterra.extend g x) x := by
  rw [← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have hc := continuous_extend g
  apply (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  exact primitive_extend_eq g y ⟨hy.1.le,hy.2.le⟩

/-- The closed spatial derivative graph is represented by a bounded
primitive operator, allowing genuine curve derivatives to pass through contours. -/
theorem curve_eq_constant_add_unitComplexCurvePrimitive
    (f g : Curve ℂ)
    (hf : AbsolutelyContinuousOnInterval (NLS.LinearVolterra.extend f) 0 1)
    (hd : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (NLS.LinearVolterra.extend f) (NLS.LinearVolterra.extend g x) x) :
    f=ContinuousMap.const _ (f ⟨0,by norm_num⟩)+unitComplexCurvePrimitive g := by
  apply ContinuousMap.ext
  intro t
  have hsub : uIcc (0 : ℝ) t.val⊆Icc (0 : ℝ) 1 := by
    rw [uIcc_of_le t.property.1]
    exact Icc_subset_Icc le_rfl t.property.2
  rw [restrict_Ioc_eq_restrict_Icc] at hd
  have hh := (ae_restrict_iff' measurableSet_Icc).mp hd
  have hi := integral_eq_sub_of_ac_of_ae_hasDerivAt
    (hf.mono (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ)≤1)] using hsub))
    ((continuous_extend g).intervalIntegrable 0 t.val) (by
      filter_upwards [hh] with x hx
      intro hxt
      exact hx (hsub hxt))
  have h0 : NLS.LinearVolterra.extend f 0=f ⟨0,by norm_num⟩ := extend_coe f ⟨0,by norm_num⟩
  rw [extend_coe,h0] at hi
  change f t=f ⟨0,by norm_num⟩+unitComplexCurvePrimitive g t
  rw [unitComplexCurvePrimitive_apply]
  linear_combination -hi

end NLS.FunctionalAnalysis
