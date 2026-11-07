import NLS.Articles.KdVPseudomeasures.OriginalHillSelectedActionDirection
import NLS.Articles.KdVPseudomeasures.OriginalHillH1ActionCurve
import NLS.Articles.KdVPseudomeasures.OriginalHillNativeJacobianInverse
import NLS.KdV.HillNativeMeanZeroDerivative

/-! The genuine H1 selected-action curve has exactly the ACTUAL
Gardner Hamiltonian tangent of its complete phase. Injectivity of the
full complex mean-zero native Jacobian determines the source tangent,
including all other closed modes. -/
noncomputable section
open Set Complex NLS.KdV NLS.Poisson NLS.WeightedCoeff
namespace NLS.Articles.KdVPseudomeasures

theorem hillIntegerSobolevEquiv_eq_nativeCoordinate
    (q : RealSignedHilbert (signedStepOrder 0 1)) (k : ℤ) :
    ((hillIntegerSobolevEquiv 1).equiv q).val.val.val k=
      hillHminusNativeCoordinate k (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q)) := by
  rw [hillIntegerSobolevEquiv_apply]
  change (hillRealSignedMap (hillIntegerSourceInclusion 1 q)).val.val.val k=_
  rw [hillRealSignedMap_coe,hillMeanZeroComplexMap_coe]
  rfl

theorem hasDerivAt_hillH1ActionCurve_rough_zero (n : ℕ+)
    (q : RealSignedHilbert (signedStepOrder 0 1)) :
    HasDerivAt (fun t : ℝ => hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 (hillH1ActionCurve n q t)))
      (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 (deriv (hillH1ActionCurve n q) 0))) 0 := by
  let L : RealSignedHilbert (signedStepOrder 0 1) →L[ℝ] PeriodOneHminusOne :=
    hillRealMeanZeroInclusion.comp (hillIntegerSourceInclusion 1)
  have hL : HasFDerivAt L L (hillH1ActionCurve n q 0) := L.hasFDerivAt
  have hc := @DifferentiableAt.hasDerivAt ℝ inferInstance
    (RealSignedHilbert (signedStepOrder 0 1)) inferInstance inferInstance (hillH1ActionCurve n q) 0
    (analyticAt_hillH1ActionCurve n q 0).differentiableAt
  have hd := @HasFDerivAt.comp_hasDerivAt ℝ inferInstance
    (RealSignedHilbert (signedStepOrder 0 1)) inferInstance inferInstance
    PeriodOneHminusOne inferInstance inferInstance (hillH1ActionCurve n q)
    (deriv (hillH1ActionCurve n q) 0) 0 L L hL hc
  simpa only [Function.comp_def] using! hd

theorem hillH1ActionCurve_native_velocity (n : ℕ+) (q : RealSignedHilbert (signedStepOrder 0 1)) (k : ℤ) :
    (fderiv ℂ (hillHminusNativeCoordinate k) (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q)))
      (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 (deriv (hillH1ActionCurve n q) 0)))=
      (hillH1ActionDirection n ((hillIntegerSobolevEquiv 1).equiv q)).val.val.val k := by
  let Q := hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q)
  have hr : IsRealPeriodOneHminusOne Q := (hillIntegerSourceInclusion 1 q).property
  have hN := ((analyticOnNhd_hillHminusNativeCoordinate k Q
    (real_mem_hillHminusActionAngleNativeDomain Q hr)).differentiableAt.hasFDerivAt.restrictScalars ℝ)
  have hd := hN.comp_hasDerivAt_of_eq 0 (hasDerivAt_hillH1ActionCurve_rough_zero n q)
    (by rw [hillH1ActionCurve_zero])
  have he : (fun t : ℝ => hillHminusNativeCoordinate k
      (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 (hillH1ActionCurve n q t))))=
      (fun t : ℝ => ((hillIntegerSobolevEquiv 1).equiv q).val.val.val k+
        (t:ℂ)*(hillH1ActionDirection n ((hillIntegerSobolevEquiv 1).equiv q)).val.val.val k) := by
    funext t
    rw [← hillIntegerSobolevEquiv_eq_nativeCoordinate,hillH1ActionCurve_native_image]
    rfl
  dsimp only [Function.comp_def] at hd
  rw [he] at hd
  have hl := ((Complex.ofRealCLM.hasDerivAt (x := (0:ℝ))).mul_const
    ((hillH1ActionDirection n ((hillIntegerSobolevEquiv 1).equiv q)).val.val.val k)).const_add
      (((hillIntegerSobolevEquiv 1).equiv q).val.val.val k)
  simpa only [Complex.ofRealCLM_apply,Complex.ofReal_one,one_mul] using! hd.unique hl

theorem hillH1ActionDirection_apply (n : ℕ+) (z : RealSignedHilbert (signedStepOrder (1/2) 1)) (k : ℤ) :
    (hillH1ActionDirection n z).val.val.val k=
      if k=(n:ℤ) then (2*z.val.val.val (-(n:ℤ)))⁻¹
      else if k=-(n:ℤ) then (2*z.val.val.val (n:ℤ))⁻¹ else 0 := by
  let f : ℤ → ℂ := fun j => z.val.val.val j
  have hf : f (-(n:ℤ))=(starRingEnd ℂ) (f (n:ℤ)) := z.property (n:ℤ)
  change (hillH1ModeCLM n ((2*(starRingEnd ℂ) (f (n:ℤ)))⁻¹)).val.val.val k=
    if k=(n:ℤ) then (2*f (-(n:ℤ)))⁻¹ else if k=-(n:ℤ) then (2*f (n:ℤ))⁻¹ else 0
  rw [hillH1ModeCLM_apply,hf]
  have hn : (n:ℤ)≠-(n:ℤ) := by
    have hp : (0:ℤ)<(n:ℤ) := by exact_mod_cast n.pos
    omega
  by_cases hk : k=(n:ℤ)
  · subst k
    simp [hn]
  · by_cases hm : k=-(n:ℤ)
    · subst k
      simp [Ne.symm hn]
      exact Or.inl (map_ofNat (starRingEnd ℂ) 2)
    · simp [hk,hm]

theorem hillH1ActionCurve_tangent_eq_phase_HamiltonianVector
    {P : HillProductEquationPatch} {n : ℕ+} (A : HillPhysicalOnIndexPhaseChart P n)
    (q : RealSignedHilbert (signedStepOrder 0 1))
    (hq : hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q) ∈ A.source) :
    hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 (deriv (hillH1ActionCurve n q) 0))=
      gardnerHamiltonianVector A.completePhase (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q)) := by
  let r := hillIntegerSourceInclusion 1 q
  let Q := hillRealMeanZeroInclusion r
  let v : HillMeanZeroSource := (hillIntegerSourceInclusion 1 (deriv (hillH1ActionCurve n q) 0)).val
  let g : HillMeanZeroSource := ⟨gardnerHamiltonianVector A.completePhase Q,
    A.completePhase_HamiltonianVector_zero_mode Q⟩
  have hdomain := real_mem_hillMeanZeroComplexDomain r.val r.property
  have hv : (fderiv ℂ hillMeanZeroComplexMap r.val) v=(fderiv ℂ hillMeanZeroComplexMap r.val) g := by
    apply Subtype.ext
    apply Subtype.ext
    funext k
    rw [fderiv_hillMeanZeroComplexMap_coordinate r.val hdomain v k,
      fderiv_hillMeanZeroComplexMap_coordinate r.val hdomain g k]
    have hc := hillH1ActionCurve_native_velocity n q k
    have hg := hillRealNativeCoordinate_phase_Hamiltonian_velocity A r hq k
    have hh := hillH1ActionDirection_apply n ((hillIntegerSobolevEquiv 1).equiv q) k
    rw [hillIntegerSobolevEquiv_eq_nativeCoordinate,hillIntegerSobolevEquiv_eq_nativeCoordinate] at hh
    exact hc.trans (hh.trans hg.symm)
  have he : v=g := (hillRealNativeJacobian_bijective r).1 hv
  exact congrArg (fun h : HillMeanZeroSource => h.val) he

theorem phase_HamiltonianVector_has_genuine_H1_representative
    {P : HillProductEquationPatch} {n : ℕ+} (A : HillPhysicalOnIndexPhaseChart P n)
    (q : RealSignedHilbert (signedStepOrder 0 1))
    (hq : hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q) ∈ A.source) :
    ∃ v : RealSignedHilbert (signedStepOrder 0 1),
      hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 v)=
        gardnerHamiltonianVector A.completePhase (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q)) :=
  ⟨deriv (hillH1ActionCurve n q) 0,hillH1ActionCurve_tangent_eq_phase_HamiltonianVector A q hq⟩

end NLS.Articles.KdVPseudomeasures
