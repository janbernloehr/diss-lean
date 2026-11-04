import NLS.KdV.HillDirichletGradients
import NLS.KdV.ClassicalHillDiscriminantGradient
import NLS.ZakharovShabat.L2CharacteristicGradients

/-! # Actual rough Hill trace-gradient curves

The scalar quadratic kernel is formed from the actual rough fundamental
states. Its potential-gradient representation follows from the proved
physical L2 IVP derivative and the actual constant-upper state bridge.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV

private def scalarPosition (A : Curve (ℂ × ℂ)) : Curve ℂ :=
  (ContinuousMap.fst : C(ℂ × ℂ,ℂ)).comp A

private def scalarVelocity (A : Curve (ℂ × ℂ)) : Curve ℂ :=
  (ContinuousMap.snd : C(ℂ × ℂ,ℂ)).comp A

/-- The literal trace-gradient density at frequency `z`, in continuous physical curves. -/
def hillL2TraceGradientCurve (q : Coeff 2) (z : ℂ) : Curve ℂ :=
  let C := hillL2FrequencyStateCurve q z (1,0)
  let S := hillL2FrequencyStateCurve q z (0,1)
  (S ⟨1,by norm_num⟩).1 • (scalarPosition C)^2+
    ((S ⟨1,by norm_num⟩).2-(C ⟨1,by norm_num⟩).1) •
      (scalarPosition C*scalarPosition S)-
    (C ⟨1,by norm_num⟩).2 • (scalarPosition S)^2

/-- Its actual spatial derivative expression, retaining rough scalar velocities. -/
def hillL2TraceGradientSpatialCurve (q : Coeff 2) (z : ℂ) : Curve ℂ :=
  let C := hillL2FrequencyStateCurve q z (1,0)
  let S := hillL2FrequencyStateCurve q z (0,1)
  (2*(S ⟨1,by norm_num⟩).1) • (scalarPosition C*scalarVelocity C)+
    ((S ⟨1,by norm_num⟩).2-(C ⟨1,by norm_num⟩).1) •
      (scalarPosition C*scalarVelocity S+scalarVelocity C*scalarPosition S)-
    (2*(C ⟨1,by norm_num⟩).2) • (scalarPosition S*scalarVelocity S)

@[simp] theorem hillL2TraceGradientCurve_apply (q : Coeff 2) (z : ℂ) (t : Icc (0 : ℝ) 1) :
    hillL2TraceGradientCurve q z t =
      (hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).1*
        (hillL2FrequencyStateCurve q z (1,0) t).1^2+
      ((hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).2-
        (hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).1)*
          (hillL2FrequencyStateCurve q z (1,0) t).1*(hillL2FrequencyStateCurve q z (0,1) t).1-
      (hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).2*
        (hillL2FrequencyStateCurve q z (0,1) t).1^2 := by
  simp only [hillL2TraceGradientCurve,scalarPosition,ContinuousMap.add_apply,
    ContinuousMap.sub_apply,ContinuousMap.smul_apply,ContinuousMap.mul_apply,
    ContinuousMap.pow_apply,ContinuousMap.comp_apply,ContinuousMap.fst_apply,smul_eq_mul]
  ring

@[simp] theorem hillL2TraceGradientSpatialCurve_apply (q : Coeff 2) (z : ℂ) (t : Icc (0 : ℝ) 1) :
    hillL2TraceGradientSpatialCurve q z t =
      2*(hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).1*
        (hillL2FrequencyStateCurve q z (1,0) t).1*(hillL2FrequencyStateCurve q z (1,0) t).2+
      ((hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).2-
        (hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).1)*
          ((hillL2FrequencyStateCurve q z (1,0) t).1*(hillL2FrequencyStateCurve q z (0,1) t).2+
            (hillL2FrequencyStateCurve q z (1,0) t).2*(hillL2FrequencyStateCurve q z (0,1) t).1)-
      2*(hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).2*
        (hillL2FrequencyStateCurve q z (0,1) t).1*(hillL2FrequencyStateCurve q z (0,1) t).2 := by
  simp only [hillL2TraceGradientSpatialCurve,scalarPosition,scalarVelocity,ContinuousMap.add_apply,
    ContinuousMap.sub_apply,ContinuousMap.smul_apply,ContinuousMap.mul_apply,
    ContinuousMap.comp_apply,ContinuousMap.fst_apply,ContinuousMap.snd_apply,smul_eq_mul]
  ring

theorem hillL2TraceGradientCurve_eq_lower_gradient (q : Coeff 2) (z : ℂ)
    (t : Icc (0 : ℝ) 1) :
    hillL2TraceGradientCurve q z t =
      -(l2DiscriminantGradient (physicalRestrictionL2 (hillFirstOrderPotential q)) z t).2 := by
  let u := physicalRestrictionL2 (hillFirstOrderPotential q)
  let e : Icc (0 : ℝ) 1 := ⟨1,by norm_num⟩
  have hc (r : Icc (0 : ℝ) 1) := congrArg (fun Y : Curve (ℂ × ℂ) => Y r)
    (l2SolutionCurve_linearCombination u z (1,-z))
  have hs (r : Icc (0 : ℝ) 1) := congrArg (fun Y : Curve (ℂ × ℂ) => Y r)
    (l2SolutionCurve_linearCombination u z (0,I))
  simp only [ContinuousMap.add_apply,ContinuousMap.smul_apply] at hc hs
  rw [hillL2TraceGradientCurve_apply]
  simp only [hillL2FrequencyStateCurve_apply]
  simp only [constantUpperInitialVector,mul_one,mul_zero,sub_zero,zero_sub]
  change _=-(l2DiscriminantGradient u z t).2
  rw [hc e,hs e,hc t,hs t]
  simp only [constantUpperStateMap_apply,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,
    smul_eq_mul,one_mul,zero_mul,zero_add,l2DiscriminantGradient,l2EndpointGradient,extend_coe,
    ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd']
  dsimp [e]
  ring_nf
  simp
  ring

theorem fderiv_hillL2Discriminant_eq_traceGradient_integral (q h : Coeff 2) (b : ℂ) :
    (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p b) q) h=
      ∫ x in (0 : ℝ)..1,-(hillPhysicalDirection h).ofLp.2 x*
        extend (hillL2TraceGradientCurve q (Complex.sqrt b)) x := by
  let z := Complex.sqrt b
  let u := physicalRestrictionL2 (hillFirstOrderPotential q)
  have ha : AnalyticAt ℂ (fun w : IntervalPairL2 => l2Discriminant w z) u :=
    (analyticOnNhd_l2Discriminant_joint (z,u) (mem_univ _)).comp
      (f := fun w : IntervalPairL2 => (z,w)) (analyticAt_const.prod analyticAt_id)
  have hd := (ha.differentiableAt.hasFDerivAt.comp
    q (hasFDerivAt_hillPhysicalPotential q)).fderiv
  change fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p b) q = _ at hd
  rw [hd,ContinuousLinearMap.comp_apply,fderiv_l2Discriminant_eq_gradient_integral]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le (by norm_num : (0 : ℝ)≤1)]
  have hm : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), x∈Icc (0 : ℝ) 1 :=
    (ae_restrict_mem measurableSet_Ioc).mono (fun _ hx => ⟨hx.1.le,hx.2⟩)
  filter_upwards [hillPhysicalDirection_upper_zero_ae h,hm] with x hx hxi
  change (hillPhysicalDirection h).ofLp.1 x=0 at hx
  rw [hx]
  change (l2DiscriminantGradient u z x).1*0+
    (l2DiscriminantGradient u z x).2*(hillPhysicalDirection h).ofLp.2 x= _
  rw [show extend (hillL2TraceGradientCurve q z) x=hillL2TraceGradientCurve q z ⟨x,hxi⟩ by
    simp only [NLS.LinearVolterra.extend,projIcc_of_mem _ hxi]]
  rw [hillL2TraceGradientCurve_eq_lower_gradient]
  ring

theorem hillL2TraceGradientCurve_eq_classical (Q : C(AddCircle (2 : ℝ),ℂ))
    (z : ℂ) (t : Icc (0 : ℝ) 1) :
    hillL2TraceGradientCurve (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) z t=
      classicalHillTracePairingKernel (hillUnitPotentialCurve Q) (z^2) t := by
  simp only [hillL2TraceGradientCurve_apply,hillL2FrequencyStateCurve_eq_classical,
    classicalHillTracePairingKernel]

theorem hillL2TraceGradientSpatialCurve_eq_classical (Q : C(AddCircle (2 : ℝ),ℂ))
    (z : ℂ) (t : Icc (0 : ℝ) 1) :
    hillL2TraceGradientSpatialCurve (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) z t=
      classicalHillTracePairingKernelDx (hillUnitPotentialCurve Q) (z^2) t := by
  simp only [hillL2TraceGradientSpatialCurve_apply,hillL2FrequencyStateCurve_eq_classical,
    classicalHillTracePairingKernelDx]

theorem continuous_hillL2TraceGradientCurve (z : ℂ) : Continuous (fun q : Coeff 2 => hillL2TraceGradientCurve q z) := by
  have hc := continuous_hillL2FrequencyStateCurve z (1,0)
  have hs := continuous_hillL2FrequencyStateCurve z (0,1)
  have hcp := (ContinuousMap.continuous_postcomp (ContinuousMap.fst : C(ℂ × ℂ,ℂ))).comp hc
  have hsp := (ContinuousMap.continuous_postcomp (ContinuousMap.fst : C(ℂ × ℂ,ℂ))).comp hs
  have hce := (continuous_eval_const (⟨1,by norm_num⟩ : Icc (0 : ℝ) 1)).comp hc
  have hse := (continuous_eval_const (⟨1,by norm_num⟩ : Icc (0 : ℝ) 1)).comp hs
  exact ((hse.fst.smul (hcp.pow 2)).add ((hse.snd.sub hce.fst).smul (hcp.mul hsp))).sub
    (hce.snd.smul (hsp.pow 2))

theorem continuous_hillL2TraceGradientSpatialCurve (z : ℂ) : Continuous (fun q : Coeff 2 => hillL2TraceGradientSpatialCurve q z) := by
  have hc := continuous_hillL2FrequencyStateCurve z (1,0)
  have hs := continuous_hillL2FrequencyStateCurve z (0,1)
  have hcp := (ContinuousMap.continuous_postcomp (ContinuousMap.fst : C(ℂ × ℂ,ℂ))).comp hc
  have hsp := (ContinuousMap.continuous_postcomp (ContinuousMap.fst : C(ℂ × ℂ,ℂ))).comp hs
  have hcv := (ContinuousMap.continuous_postcomp (ContinuousMap.snd : C(ℂ × ℂ,ℂ))).comp hc
  have hsv := (ContinuousMap.continuous_postcomp (ContinuousMap.snd : C(ℂ × ℂ,ℂ))).comp hs
  have hce := (continuous_eval_const (⟨1,by norm_num⟩ : Icc (0 : ℝ) 1)).comp hc
  have hse := (continuous_eval_const (⟨1,by norm_num⟩ : Icc (0 : ℝ) 1)).comp hs
  exact (((continuous_const.mul hse.fst).smul (hcp.mul hcv)).add
    ((hse.snd.sub hce.fst).smul ((hcp.mul hsv).add (hcv.mul hsp)))).sub
      ((continuous_const.mul hce.snd).smul (hsp.mul hsv))

theorem continuous_hillL2TraceGradientSpatialCurve_frequency (q : Coeff 2) : Continuous (fun z : ℂ => hillL2TraceGradientSpatialCurve q z) := by
  have hc := continuous_hillL2FrequencyStateCurve_frequency q (1,0)
  have hs := continuous_hillL2FrequencyStateCurve_frequency q (0,1)
  have hcp := (ContinuousMap.continuous_postcomp (ContinuousMap.fst : C(ℂ × ℂ,ℂ))).comp hc
  have hsp := (ContinuousMap.continuous_postcomp (ContinuousMap.fst : C(ℂ × ℂ,ℂ))).comp hs
  have hcv := (ContinuousMap.continuous_postcomp (ContinuousMap.snd : C(ℂ × ℂ,ℂ))).comp hc
  have hsv := (ContinuousMap.continuous_postcomp (ContinuousMap.snd : C(ℂ × ℂ,ℂ))).comp hs
  have hce := (continuous_eval_const (⟨1,by norm_num⟩ : Icc (0 : ℝ) 1)).comp hc
  have hse := (continuous_eval_const (⟨1,by norm_num⟩ : Icc (0 : ℝ) 1)).comp hs
  exact (((continuous_const.mul hse.fst).smul (hcp.mul hcv)).add
    ((hse.snd.sub hce.fst).smul ((hcp.mul hsv).add (hcv.mul hsp)))).sub
      ((continuous_const.mul hce.snd).smul (hsp.mul hsv))

theorem ae_hasDerivAt_hillL2TraceGradientCurve (q : Coeff 2) (z : ℂ) :
    ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (extend (hillL2TraceGradientCurve q z))
        (extend (hillL2TraceGradientSpatialCurve q z) x) x := by
  let C := hillL2FrequencyStateCurve q z (1,0)
  let S := hillL2FrequencyStateCurve q z (0,1)
  let e : Icc (0 : ℝ) 1 := ⟨1,by norm_num⟩
  have he : extend (hillL2TraceGradientCurve q z) =
      (fun x => (S e).1*(extend C x).1^2+
        ((S e).2-(C e).1)*(extend C x).1*(extend S x).1-(C e).2*(extend S x).1^2) := by
    funext x
    simp only [NLS.LinearVolterra.extend,hillL2TraceGradientCurve_apply]
    rfl
  filter_upwards [ae_hasDerivAt_hillL2FrequencyStateCurve_fst q z (1,0),
    ae_hasDerivAt_hillL2FrequencyStateCurve_fst q z (0,1)] with x hc hs
  rw [he]
  convert! (((hc.pow 2).const_mul (S e).1).add
    ((hc.const_mul ((S e).2-(C e).1)).mul hs)).sub ((hs.pow 2).const_mul (C e).2) using 1
  simp only [NLS.LinearVolterra.extend,hillL2TraceGradientSpatialCurve_apply]
  dsimp [C,S,e]
  ring

end NLS.KdV
