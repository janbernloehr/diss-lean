import NLS.ZakharovShabat.CentralCircleThresholds
import NLS.KdV.HillCubicFrequencyCircle
import NLS.KdV.HillDirichletInterpolationExterior

/-! # Comparing actual cubic spectral contours with Dirichlet contours -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ContDiff ComplexConjugate
namespace NLS.KdV

theorem exists_hillL2CubicFrequency_contour_error_bound
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hreal : ∀ x : AddCircle (2:ℝ), (Q x).im=0)
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)
    (hmean : (∫ x in (0:ℝ)..1, Q (x : AddCircle (2:ℝ)))=0)
    (n : ℕ) (hn : 1≤n) :
    let q := hillContinuousCoefficients Q
    let f := fun E => hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) E^3*
      hillAbelianSelectedGlobalPsi q hq hr n hn E/hillL2RealCutRoot (SpectralWeight.one.toCoeff q) E
    let g := fun E => (-E/2-Q (0 : AddCircle (2:ℝ))/4)*
      (hillAbelianSelectedGlobalPsi q hq hr n hn E/hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E)
    ∃ C : ℝ, 0<C ∧ ∃ K : ℕ, ∀ M : ℕ, K≤M →
      CircleIntegrable f 0 ((centralCircleRadius M)^2) ∧
      CircleIntegrable g 0 ((centralCircleRadius M)^2) ∧
      centralCircleRadius M *
        ‖(∮ E in C(0,(centralCircleRadius M)^2), f E)-
          (∮ E in C(0,(centralCircleRadius M)^2), g E)‖≤C := by
  dsimp only
  let q := hillContinuousCoefficients Q
  let f := fun E => hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) E^3*
    hillAbelianSelectedGlobalPsi q hq hr n hn E/hillL2RealCutRoot (SpectralWeight.one.toCoeff q) E
  let g := fun E => (-E/2-Q (0 : AddCircle (2:ℝ))/4)*
    (hillAbelianSelectedGlobalPsi q hq hr n hn E/hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E)
  obtain ⟨A,hA,KA,hkernel⟩ := exists_hillL2CubicDirichletKernel_circle_error_bound Q hq hr hreal hf hp hmean
  obtain ⟨KB,B,hB,hquot⟩ := eventually_hillAbelianSelectedGlobalPsi_dirichlet_circle_bound q hq hr n hn
  obtain ⟨KR,hroot⟩ := eventually_atTop.mp (eventually_hillL2RealCutRoot_circle_ne_zero Q hq hr hf hp)
  have hrad (M : ℕ) : hillFreeBandFrequency M=centralCircleRadius M := by
    unfold hillFreeBandFrequency centralCircleRadius
    ring
  refine ⟨2*Real.pi*A*B,by positivity,max (max KA KB) KR,?_⟩
  intro M hM
  let r := centralCircleRadius M
  have hrp : 0<r := centralCircleRadius_pos M
  have hR : ∀ E∈sphere (0:ℂ) (r^2), hillL2RealCutRoot (SpectralWeight.one.toCoeff q) E≠0 := by
    simpa only [hrad] using hroot M ((le_max_right _ _).trans hM)
  have hD : ∀ E∈sphere (0:ℂ) (r^2), hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E≠0 :=
    fun E hE => (hquot M ((le_max_right _ _).trans ((le_max_left _ _).trans hM)) E hE).1
  have hfi : CircleIntegrable f 0 (r^2) := circleIntegrable_hillL2CubicFrequencyIntegrand q hq hr n hn _
    (sq_pos_of_pos hrp) hR
  have hgi : CircleIntegrable g 0 (r^2) := circleIntegrable_hillDirichletPolynomialIntegrand q hq hr n hn _ _
    (sq_pos_of_pos hrp) hD
  refine ⟨hfi,hgi,?_⟩
  have hpoint (E : ℂ) (hE : E∈sphere (0:ℂ) (r^2)) : ‖f E-g E‖≤A*B/r^3 := by
    let F := hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) E
    let D := hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E
    let R := hillL2RealCutRoot (SpectralWeight.one.toCoeff q) E
    let ψ := hillAbelianSelectedGlobalPsi q hq hr n hn E
    have hk := hkernel M ((le_max_left _ _).trans ((le_max_left _ _).trans hM)) E (by simpa only [hrad] using hE)
    rw [hrad] at hk
    change r*‖F^3*(D/R)+E/2+Q (0 : AddCircle (2:ℝ))/4‖≤A at hk
    have hψ := (hquot M ((le_max_right _ _).trans ((le_max_left _ _).trans hM)) E hE).2
    change ‖ψ/D‖≤B/r^2 at hψ
    have hψw : r^2*‖ψ/D‖≤B := by
      have hh := (le_div_iff₀ (sq_pos_of_pos hrp)).mp hψ
      simpa only [mul_comm] using hh
    have he : f E-g E=(F^3*(D/R)+E/2+Q (0 : AddCircle (2:ℝ))/4)*(ψ/D) := by
      dsimp only [f,g,F,D,R,ψ]
      field_simp [hD E hE,hR E hE]
      ring
    apply (le_div_iff₀ (pow_pos hrp 3)).mpr
    rw [he,norm_mul]
    calc
      _ = (r*‖F^3*(D/R)+E/2+Q (0 : AddCircle (2:ℝ))/4‖)*(r^2*‖ψ/D‖) := by ring
      _ ≤ A*B := mul_le_mul hk hψw (by positivity) hA.le
  rw [← circleIntegral.integral_sub hfi hgi]
  have hI := circleIntegral.norm_integral_le_of_norm_le_const (sq_nonneg r) hpoint
  calc
    _ ≤ r*(2*Real.pi*r^2*(A*B/r^3)) := mul_le_mul_of_nonneg_left hI hrp.le
    _ = 2*Real.pi*A*B := by field_simp

/-- The two genuine contour integrals differ by a quantity tending to zero.
No finite-gap assumption is needed for this comparison. -/
theorem tendsto_hillL2CubicFrequency_contour_sub_dirichlet
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hreal : ∀ x : AddCircle (2:ℝ), (Q x).im=0)
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)
    (hmean : (∫ x in (0:ℝ)..1, Q (x : AddCircle (2:ℝ)))=0)
    (n : ℕ) (hn : 1≤n) :
    let q := hillContinuousCoefficients Q
    Tendsto (fun M : ℕ =>
      (∮ E in C(0,(centralCircleRadius M)^2),
        hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) E^3*
          hillAbelianSelectedGlobalPsi q hq hr n hn E/hillL2RealCutRoot (SpectralWeight.one.toCoeff q) E)-
      (∮ E in C(0,(centralCircleRadius M)^2), (-E/2-Q (0 : AddCircle (2:ℝ))/4)*
        (hillAbelianSelectedGlobalPsi q hq hr n hn E/hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E)))
      atTop (𝓝 0) := by
  dsimp only
  obtain ⟨C,_hC,K,hbound⟩ := exists_hillL2CubicFrequency_contour_error_bound Q hq hr hreal hf hp hmean n hn
  have hlim : Tendsto (fun M => C/centralCircleRadius M) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Pi.inv_apply] using!
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
