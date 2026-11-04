import NLS.KdV.HillCubicFrequencyCircle
import NLS.KdV.HillQuinticFrequencyKernel
import NLS.KdV.HillIntrinsicOddFrequencyPeriods
import NLS.KdV.HillDirichletInterpolationExterior
import NLS.ZakharovShabat.CentralCircleThresholds

/-! # Actual quintic spectral versus mass-corrected Dirichlet contour comparison -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ContDiff
namespace NLS.KdV

theorem exists_hillFiniteGap_quintic_contour_error_bound
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hreal : ∀ x : AddCircle (2:ℝ), (Q x).im=0)
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)
    (hmean : (∫ x in (0:ℝ)..1, Q (x : AddCircle (2:ℝ)))=0)
    (n N : ℕ) (hn : 1≤n)
    (hclosed : ∀ (k : ℕ) (_hk : 1≤k), N<k → hillRealGapHalfLength (hillContinuousCoefficients Q) hq hr k=0) :
    let q := hillContinuousCoefficients Q
    let f := hillL2OddKernel q 2 (hillAbelianSelectedGlobalPsi q hq hr n hn)
    let g := fun E => (E^2/2+Q (0 : AddCircle (2:ℝ))*E/4+
      (3*Q (0 : AddCircle (2:ℝ))^2-deriv (deriv (fun x : ℝ => Q (x : AddCircle (2:ℝ)))) 0)/16-
      5*classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2:ℝ)))/8)*(hillAbelianSelectedGlobalPsi q hq hr n hn E/
      hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E)
    ∃ C : ℝ, 0<C ∧ ∃ K : ℕ, ∀ M : ℕ, K≤M →
      CircleIntegrable f 0 ((centralCircleRadius M)^2) ∧
      CircleIntegrable g 0 ((centralCircleRadius M)^2) ∧
      centralCircleRadius M*‖(∮ E in C(0,(centralCircleRadius M)^2), f E)-
        (∮ E in C(0,(centralCircleRadius M)^2), g E)‖≤C := by
  dsimp only
  let q := hillContinuousCoefficients Q
  let P := hillAbelianSelectedGlobalPsi q hq hr n hn
  let f := hillL2OddKernel q 2 P
  let g := fun E => (E^2/2+Q (0 : AddCircle (2:ℝ))*E/4+
      (3*Q (0 : AddCircle (2:ℝ))^2-deriv (deriv (fun x : ℝ => Q (x : AddCircle (2:ℝ)))) 0)/16-
      5*classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2:ℝ)))/8)*(P E/hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E)
  have hP : AnalyticOnNhd ℂ P univ := analyticOnNhd_hillAbelianSelectedGlobalPsi_energy q hq hr n hn
  have hfg : HillFiniteGap q hq hr := by
    apply (hillFiniteGap_iff_collapsed_tail q hq hr).2
    refine ⟨N+1,?_⟩
    intro k hk hk1
    have hh := hclosed k hk1 (by omega)
    dsimp only [hillRealGapHalfLength] at hh
    linarith
  obtain ⟨R,_hR,_ha,hperiod⟩ := HillFiniteGap.exists_odd_exterior_and_periods q hq hr hfg 2 n hn
  obtain ⟨A,hA,KA,hkernel⟩ := exists_hillL2QuinticDirichletKernel_circle_error_bound Q hq hr hreal hf hp hmean
  obtain ⟨KB,B,hB,hquot⟩ := eventually_hillAbelianSelectedGlobalPsi_dirichlet_circle_bound q hq hr n hn
  obtain ⟨KR,hroot⟩ := eventually_atTop.mp (eventually_hillL2RealCutRoot_circle_ne_zero Q hq hr hf hp)
  have hlarge : ∀ᶠ M : ℕ in atTop, R<(centralCircleRadius M)^2 := by
    filter_upwards [tendsto_centralCircleRadius_atTop.eventually_gt_atTop (max R 1)] with M hM
    have hMR : R<centralCircleRadius M := (le_max_left _ _).trans_lt hM
    have hM1 : 1<centralCircleRadius M := (le_max_right _ _).trans_lt hM
    nlinarith
  obtain ⟨KL,hKL⟩ := eventually_atTop.mp hlarge
  have hrad (M : ℕ) : hillFreeBandFrequency M=centralCircleRadius M := by
    unfold hillFreeBandFrequency centralCircleRadius
    ring
  refine ⟨2*Real.pi*A*B,by positivity,max (max KA KB) (max KR KL),?_⟩
  intro M hM
  let r := centralCircleRadius M
  have hrp : 0<r := centralCircleRadius_pos M
  have hR : ∀ E∈sphere (0:ℂ) (r^2), hillL2RealCutRoot (SpectralWeight.one.toCoeff q) E≠0 := by
    simpa only [hrad] using hroot M ((le_max_left _ _).trans ((le_max_right _ _).trans hM))
  have hD : ∀ E∈sphere (0:ℂ) (r^2), hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E≠0 :=
    fun E hE => (hquot M ((le_max_right _ _).trans ((le_max_left _ _).trans hM)) E hE).1
  have hfi : CircleIntegrable f 0 (r^2) :=
    (hperiod _ (hKL M ((le_max_right _ _).trans ((le_max_right _ _).trans hM)))).1
  have hgi : CircleIntegrable g 0 (r^2) := by
    apply ContinuousOn.circleIntegrable (sq_nonneg r)
    intro E hE
    have hm : AnalyticAt ℂ (fun E : ℂ => (E^2/2+Q (0 : AddCircle (2:ℝ))*E/4+
      (3*Q (0 : AddCircle (2:ℝ))^2-deriv (deriv (fun x : ℝ => Q (x : AddCircle (2:ℝ)))) 0)/16-
      5*classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2:ℝ)))/8)) E := by fun_prop
    exact (hm.mul ((hP E (mem_univ _)).div
      (analyticOnNhd_hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E (mem_univ _))
      (hD E hE))).continuousAt.continuousWithinAt
  refine ⟨hfi,hgi,?_⟩
  have hpoint (E : ℂ) (hE : E∈sphere (0:ℂ) (r^2)) : ‖f E-g E‖≤A*B/r^3 := by
    let F := hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) E
    let D := hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E
    let T := hillL2RealCutRoot (SpectralWeight.one.toCoeff q) E
    let ψ := P E
    have hk := hkernel M ((le_max_left _ _).trans ((le_max_left _ _).trans hM)) E (by simpa only [hrad] using hE)
    rw [hrad] at hk
    change r*‖F^5*(D/T)-(E^2/2+Q (0 : AddCircle (2:ℝ))*E/4+
      (3*Q (0 : AddCircle (2:ℝ))^2-deriv (deriv (fun x : ℝ => Q (x : AddCircle (2:ℝ)))) 0)/16-
      5*classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2:ℝ)))/8)‖≤A at hk
    have hψ := (hquot M ((le_max_right _ _).trans ((le_max_left _ _).trans hM)) E hE).2
    change ‖ψ/D‖≤B/r^2 at hψ
    have hψw : r^2*‖ψ/D‖≤B := by
      have hh := (le_div_iff₀ (sq_pos_of_pos hrp)).mp hψ
      simpa only [mul_comm] using hh
    have he : f E-g E=(F^5*(D/T)-(E^2/2+Q (0 : AddCircle (2:ℝ))*E/4+
      (3*Q (0 : AddCircle (2:ℝ))^2-deriv (deriv (fun x : ℝ => Q (x : AddCircle (2:ℝ)))) 0)/16-
      5*classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2:ℝ)))/8))*(ψ/D) := by
      dsimp only [f,g,hillL2OddKernel,Nat.reduceMul,Nat.reduceAdd,F,D,T,ψ]
      field_simp [hD E hE,hR E hE]
    apply (le_div_iff₀ (pow_pos hrp 3)).mpr
    rw [he,norm_mul]
    calc
      _ = (r*‖F^5*(D/T)-(E^2/2+Q (0 : AddCircle (2:ℝ))*E/4+
      (3*Q (0 : AddCircle (2:ℝ))^2-deriv (deriv (fun x : ℝ => Q (x : AddCircle (2:ℝ)))) 0)/16-
      5*classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2:ℝ)))/8)‖)*(r^2*‖ψ/D‖) := by ring
      _ ≤ A*B := mul_le_mul hk hψw (by positivity) hA.le
  rw [← circleIntegral.integral_sub hfi hgi]
  have hI := circleIntegral.norm_integral_le_of_norm_le_const (sq_nonneg r) hpoint
  calc
    _ ≤ r*(2*Real.pi*r^2*(A*B/r^3)) := mul_le_mul_of_nonneg_left hI hrp.le
    _ = 2*Real.pi*A*B := by field_simp

/-- The genuine quintic spectral and mass-corrected Dirichlet contour difference
tends to zero, with inverse frequency error. -/
theorem tendsto_hillFiniteGap_quintic_contour_sub_dirichlet
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hreal : ∀ x : AddCircle (2:ℝ), (Q x).im=0)
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)
    (hmean : (∫ x in (0:ℝ)..1, Q (x : AddCircle (2:ℝ)))=0)
    (n N : ℕ) (hn : 1≤n)
    (hclosed : ∀ (k : ℕ) (_hk : 1≤k), N<k → hillRealGapHalfLength (hillContinuousCoefficients Q) hq hr k=0) :
    let q := hillContinuousCoefficients Q
    Tendsto (fun M : ℕ => (∮ E in C(0,(centralCircleRadius M)^2),
      hillL2OddKernel q 2 (hillAbelianSelectedGlobalPsi q hq hr n hn) E)-
      (∮ E in C(0,(centralCircleRadius M)^2), (E^2/2+Q (0 : AddCircle (2:ℝ))*E/4+
      (3*Q (0 : AddCircle (2:ℝ))^2-deriv (deriv (fun x : ℝ => Q (x : AddCircle (2:ℝ)))) 0)/16-
      5*classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2:ℝ)))/8)*
        (hillAbelianSelectedGlobalPsi q hq hr n hn E/hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E)))
      atTop (𝓝 0) := by
  dsimp only
  obtain ⟨C,_hC,K,hbound⟩ := exists_hillFiniteGap_quintic_contour_error_bound Q hq hr hreal hf hp hmean n N hn hclosed
  have hlim : Tendsto (fun M => C/centralCircleRadius M) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Pi.inv_apply] using
      tendsto_centralCircleRadius_atTop.inv_tendsto_atTop.const_mul C
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [eventually_ge_atTop K,hlim.eventually (gt_mem_nhds hε)] with M hM hsmall
  rw [dist_zero_right]
  have hb := (hbound M hM).2.2
  apply lt_of_le_of_lt ?_ hsmall
  apply (le_div_iff₀ (centralCircleRadius_pos M)).mpr
  simpa only [mul_comm (centralCircleRadius M)] using hb

end NLS.KdV
