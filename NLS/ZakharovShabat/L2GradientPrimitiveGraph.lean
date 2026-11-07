import NLS.ZakharovShabat.L2DiscriminantXiIntegral
import NLS.FunctionalAnalysis.UnitComplexCurvePrimitive

/-! # The spatial gradient equation as a bounded primitive graph

Both rows use actual L2 Volterra operators and ordinary continuous primitives.
This form can pass through a Banach-valued spectral contour without assuming
that its pointwise spatial exceptional sets are uniform in the spectral variable.
-/
noncomputable section
open Set Complex Filter Topology MeasureTheory NLS.LinearVolterra NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

def gradientFirstCurve : Curve (ℂ × ℂ) →L[ℂ] Curve ℂ :=
  ContinuousLinearMap.compLeftContinuous ℂ _ (ContinuousLinearMap.fst ℂ ℂ ℂ)

def gradientSecondCurve : Curve (ℂ × ℂ) →L[ℂ] Curve ℂ :=
  ContinuousLinearMap.compLeftContinuous ℂ _ (ContinuousLinearMap.snd ℂ ℂ ℂ)

def l2DiscriminantXiCurve (u : IntervalPairL2) (z : ℂ) : Curve ℂ :=
  ⟨fun t => l2DiscriminantXi u z t,by
    have ha : Continuous (fun t : Icc (0:ℝ) 1 => extend (l2SolutionCurve u z (1,0)) t) :=
      (continuous_extend _).comp continuous_subtype_val
    have hb : Continuous (fun t : Icc (0:ℝ) 1 => extend (l2SolutionCurve u z (0,1)) t) :=
      (continuous_extend _).comp continuous_subtype_val
    change Continuous (fun t : Icc (0:ℝ) 1 => l2DiscriminantXi u z t)
    dsimp only [l2DiscriminantXi,discriminantXiState]
    fun_prop⟩

theorem absolutelyContinuous_l2DiscriminantGradient_components (u : IntervalPairL2) (z : ℂ) :
    AbsolutelyContinuousOnInterval (fun x => (l2DiscriminantGradient u z x).1) 0 1 ∧
      AbsolutelyContinuousOnInterval (fun x => (l2DiscriminantGradient u z x).2) 0 1 := by
  have ha := absolutelyContinuousOnInterval_l2SolutionCurve u z (1,0)
  have hb := absolutelyContinuousOnInterval_l2SolutionCurve u z (0,1)
  have ha1 := absolutelyContinuousOnInterval_clm ha (ContinuousLinearMap.fst ℝ ℂ ℂ)
  have ha2 := absolutelyContinuousOnInterval_clm ha (ContinuousLinearMap.snd ℝ ℂ ℂ)
  have hb1 := absolutelyContinuousOnInterval_clm hb (ContinuousLinearMap.fst ℝ ℂ ℂ)
  have hb2 := absolutelyContinuousOnInterval_clm hb (ContinuousLinearMap.snd ℝ ℂ ℂ)
  have h1 := ((((ha2.smul hb2).const_smul ((l2Monodromy u z) 0 0-(l2Monodromy u z) 1 1)).sub
    ((ha2.smul ha2).const_smul ((l2Monodromy u z) 0 1))).add
      ((hb2.smul hb2).const_smul ((l2Monodromy u z) 1 0))).const_smul I
  have h2 := ((((ha1.smul hb1).const_smul ((l2Monodromy u z) 0 0-(l2Monodromy u z) 1 1)).sub
    ((ha1.smul ha1).const_smul ((l2Monodromy u z) 0 1))).add
      ((hb1.smul hb1).const_smul ((l2Monodromy u z) 1 0))).const_smul I
  constructor
  · convert! h1 using 1
    funext x
    rw [l2DiscriminantGradient_eq_state]
    dsimp [discriminantGradientState]
    ring
  · convert! h2 using 1
    funext x
    rw [l2DiscriminantGradient_eq_state]
    dsimp [discriminantGradientState]
    ring

@[simp] theorem extend_gradientFirstCurve (g : Curve (ℂ × ℂ)) (x : ℝ) :
    extend (gradientFirstCurve g) x = (extend g x).1 := rfl

@[simp] theorem extend_gradientSecondCurve (g : Curve (ℂ × ℂ)) (x : ℝ) :
    extend (gradientSecondCurve g) x = (extend g x).2 := rfl

theorem curve_eq_mixed_primitive_of_ac (f g h : Curve ℂ) (u : IntervalL2) (a b : ℂ)
    (hf : AbsolutelyContinuousOnInterval (extend f) 0 1)
    (hd : ∀ᵐ x ∂volume.restrict (Ioc (0:ℝ) 1),
      HasDerivAt (extend f) (a*extend g x+b*(u x*extend h x)) x) :
    f = ContinuousMap.const _ (f ⟨0,by norm_num⟩)+
      a • unitComplexCurvePrimitive g+b • l2ScalarVolterra u h := by
  apply ContinuousMap.ext
  intro t
  have hs : uIcc (0:ℝ) t.val ⊆ uIcc (0:ℝ) 1 := by
    rw [uIcc_of_le t.property.1,uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl t.property.2
  have hig : IntervalIntegrable (extend g) volume 0 t.val :=
    (continuous_extend g).intervalIntegrable 0 t.val
  have hih := intervalIntegrable_intervalL2_mul u (curveBoundedExtension ℂ h) t
  have hefilter : ae (volume.restrict (Ioc (0:ℝ) 1)) = ae (volume.restrict (Icc (0:ℝ) 1)) :=
    congrArg (fun μ : Measure ℝ => ae μ) restrict_Ioc_eq_restrict_Icc
  have hdcc := hefilter ▸ hd
  have hdglobal := (ae_restrict_iff' measurableSet_Icc).mp hdcc
  have hdt : ∀ᵐ x : ℝ, x ∈ uIcc (0:ℝ) t.val →
      HasDerivAt (extend f) (a*extend g x+b*(u x*extend h x)) x := by
    filter_upwards [hdglobal] with x hx hxt
    exact hx (by simpa using hs hxt)
  have hi := integral_eq_sub_of_ac_of_ae_hasDerivAt (hf.mono hs)
    ((hig.const_mul a).add (hih.const_mul b)) hdt
  rw [intervalIntegral.integral_add (hig.const_mul a) (hih.const_mul b),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    extend_coe f t,extend_coe f ⟨0,by norm_num⟩] at hi
  change f t = f ⟨0,by norm_num⟩+a*unitComplexCurvePrimitive g t+b*l2ScalarVolterra u h t
  rw [unitComplexCurvePrimitive_apply,l2ScalarVolterra_apply]
  change a*(∫ x in (0:ℝ)..t.val, extend g x)+
    b*(∫ x in (0:ℝ)..t.val, u x*extend h x) = f t-f ⟨0,by norm_num⟩ at hi
  linear_combination -hi

/-- One scalar primitive graph recovers AC and the actual AE derivative. -/
theorem curve_regular_of_primitive_graph (f g h : Curve ℂ) (u : IntervalL2) (a b : ℂ)
    (he : f = ContinuousMap.const _ (f ⟨0,by norm_num⟩)+
      a • unitComplexCurvePrimitive g+b • l2ScalarVolterra u h) :
    AbsolutelyContinuousOnInterval (extend f) 0 1 ∧
      ∀ᵐ x ∂volume.restrict (Ioc (0:ℝ) 1),
        HasDerivAt (extend f) (a*extend g x+b*u x*extend h x) x := by
  have hi := intervalIntegrable_intervalL2_mul u (curveBoundedExtension ℂ h) ⟨1,by norm_num⟩
  have hprimitive := absolutelyContinuousOnInterval_integral hi (c := (0:ℝ)) (by simp)
  have hsum := absolutelyContinuousOnInterval_const_add
    ((absolutelyContinuousOnInterval_clm (absolutelyContinuousOnInterval_unitComplexCurvePrimitive g)
      ((a • ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ)).add
      (absolutelyContinuousOnInterval_clm hprimitive
        ((b • ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ))) (f ⟨0,by norm_num⟩)
  have hx (x : ℝ) (hxi : x ∈ Icc (0:ℝ) 1) : extend f x =
      f ⟨0,by norm_num⟩+(a*extend (unitComplexCurvePrimitive g) x+
        b*(∫ t in (0:ℝ)..x, u t*extend h t)) := by
    rw [extend_coe f ⟨x,hxi⟩,extend_coe _ ⟨x,hxi⟩]
    have e := congrArg (fun v : Curve ℂ => v ⟨x,hxi⟩) he
    simpa only [extend_coe,ContinuousMap.add_apply,ContinuousMap.const_apply,
      ContinuousMap.smul_apply,smul_eq_mul,l2ScalarVolterra_apply,add_assoc] using e
  refine ⟨absolutelyContinuousOnInterval_congr hsum (fun x hxi => (hx x (by
    simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hxi)).symm),?_⟩
  have hid := ae_restrict_of_ae (s := Ioc (0:ℝ) 1) hi.ae_hasDerivAt_integral
  filter_upwards [ae_hasDerivAt_unitComplexCurvePrimitive g,hid,ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae (show ∀ᵐ x : ℝ, x ≠ (1:ℝ) from by simp [ae_iff,measure_singleton])]
    with x hxg hxh hxi hx1
  have hxd := hxh (show x ∈ uIcc (0:ℝ) 1 by simpa using ⟨hxi.1.le,hxi.2⟩) 0 (by simp)
  have hd := ((hxg.const_mul a).add (hxd.const_mul b)).const_add (f ⟨0,by norm_num⟩)
  have heq : extend f =ᶠ[𝓝 x]
      (fun y => f ⟨0,by norm_num⟩+(a*extend (unitComplexCurvePrimitive g) y+
        b*(∫ t in (0:ℝ)..y, u t*extend h t))) := by
    filter_upwards [Ioo_mem_nhds hxi.1 (lt_of_le_of_ne hxi.2 hx1)] with y hy
    exact hx y ⟨hy.1.le,hy.2.le⟩
  convert! hd.congr_of_eventuallyEq heq using 1
  simp only [mul_assoc,curveBoundedExtension_apply]

theorem l2DiscriminantGradient_first_primitive_graph (u : IntervalPairL2) (z : ℂ) :
    gradientFirstCurve (l2DiscriminantGradientCurve u z) =
      ContinuousMap.const _ (gradientFirstCurve (l2DiscriminantGradientCurve u z) ⟨0,by norm_num⟩)+
        (2*I*z) • unitComplexCurvePrimitive (gradientFirstCurve (l2DiscriminantGradientCurve u z))+
          (1:ℂ) • l2ScalarVolterra u.snd (l2DiscriminantXiCurve u z) := by
  have he : extend (gradientFirstCurve (l2DiscriminantGradientCurve u z)) =
      (fun x => (l2DiscriminantGradient u z x).1) := by
    funext x
    rw [extend_gradientFirstCurve,extend_l2DiscriminantGradientCurve]
  apply curve_eq_mixed_primitive_of_ac
  · rw [he]
    exact (absolutelyContinuous_l2DiscriminantGradient_components u z).1
  · filter_upwards [ae_hasDerivAt_l2DiscriminantGradient u z,ae_restrict_mem measurableSet_Ioc]
      with x hx hxi
    have hx' : x ∈ Icc (0:ℝ) 1 := ⟨hxi.1.le,hxi.2⟩
    have h := HasFDerivAt.hasDerivAt hx.fst
    rw [he]
    have hxe : extend (l2DiscriminantXiCurve u z) x = l2DiscriminantXi u z x :=
      extend_coe (l2DiscriminantXiCurve u z) ⟨x,hx'⟩
    simpa only [extend_gradientFirstCurve,extend_l2DiscriminantGradientCurve,hxe,
      one_mul,intervalL2Representative, mul_comm (l2DiscriminantXi u z x),
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.toSpanSingleton_apply,one_smul] using! h

theorem l2DiscriminantGradient_second_primitive_graph (u : IntervalPairL2) (z : ℂ) :
    gradientSecondCurve (l2DiscriminantGradientCurve u z) =
      ContinuousMap.const _ (gradientSecondCurve (l2DiscriminantGradientCurve u z) ⟨0,by norm_num⟩)+
        (-2*I*z) • unitComplexCurvePrimitive (gradientSecondCurve (l2DiscriminantGradientCurve u z))+
          (-1:ℂ) • l2ScalarVolterra u.fst (l2DiscriminantXiCurve u z) := by
  have he : extend (gradientSecondCurve (l2DiscriminantGradientCurve u z)) =
      (fun x => (l2DiscriminantGradient u z x).2) := by
    funext x
    rw [extend_gradientSecondCurve,extend_l2DiscriminantGradientCurve]
  apply curve_eq_mixed_primitive_of_ac
  · rw [he]
    exact (absolutelyContinuous_l2DiscriminantGradient_components u z).2
  · filter_upwards [ae_hasDerivAt_l2DiscriminantGradient u z,ae_restrict_mem measurableSet_Ioc]
      with x hx hxi
    have hx' : x ∈ Icc (0:ℝ) 1 := ⟨hxi.1.le,hxi.2⟩
    have h := HasFDerivAt.hasDerivAt hx.snd
    rw [he]
    have hxe : extend (l2DiscriminantXiCurve u z) x = l2DiscriminantXi u z x :=
      extend_coe (l2DiscriminantXiCurve u z) ⟨x,hx'⟩
    simpa only [extend_gradientSecondCurve,extend_l2DiscriminantGradientCurve,hxe,
      neg_one_mul,sub_eq_add_neg,intervalL2Representative,
      mul_comm (l2DiscriminantXi u z x),mul_neg,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.toSpanSingleton_apply,one_smul] using! h

end NLS.ZakharovShabat
