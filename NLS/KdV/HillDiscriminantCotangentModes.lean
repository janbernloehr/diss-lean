import NLS.KdV.HillClosedCurveDirections
import NLS.KdV.HillDiscriminantSourceBounds
import NLS.FunctionalAnalysis.UnitComplexCurvePrimitive

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- Each original coefficient unit mode has its literal physical period-two
wave on the unit interval, with the original constant-upper embedding sign. -/
theorem hillPhysicalDirection_single_lower_ae (n : ℤ) :
    ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      -(hillPhysicalDirection (lp.single 2 n 1)).ofLp.2 x=Fourier.wave n x := by
  let Q : C(AddCircle (2 : ℝ),ℂ) := fourier n
  have hc : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)=(lp.single 2 n 1 : Coeff 2) := by
    rw [toCoeff_hillContinuousCoefficients]
    ext k
    simp only [Q,Fourier.continuousFourierCLM_apply,fourierCoeff_fourier,lp.single_apply]
  have hh := hillPhysicalDirection_continuous_coefficients Q
  rw [hc] at hh
  filter_upwards [hh,ae_restrict_mem measurableSet_Ioc] with x hx hxi
  rw [hx]
  dsimp only [NLS.LinearVolterra.extend,hillUnitPotentialCurve,ContinuousMap.coe_mk]
  rw [projIcc_of_mem _ (show x∈Icc (0 : ℝ) 1 from ⟨hxi.1.le,hxi.2⟩)]
  exact Fourier.fourier_two_eq_wave n x

/-- Actual coefficient cotangents are the literal unit-interval wave integrals
of the physical Hill discriminant gradient. -/
theorem hillDiscriminantCotangent_single_integral (q : Coeff 2) (E : ℂ) (n : ℤ) :
    (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E) q) (lp.single 2 n 1)=
      ∫ x in (0 : ℝ)..1, NLS.LinearVolterra.extend (hillEnergyDiscriminantGradientCurve q E) x*Fourier.wave n x := by
  rw [hillEnergyDiscriminantGradient_represents_potential,hillPhysicalDirectionPairing_apply]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le (by norm_num : (0 : ℝ)≤1)]
  filter_upwards [hillPhysicalDirection_single_lower_ae n] with x hx
  rw [hx,mul_comm]

/-- Bounded complex source and energy balls have uniform bounds for the
actual physical trace gradient and its actual continuous spatial derivative. -/
theorem exists_hillDiscriminantGradient_uniform_curve_bounds
    (B R : ℝ) (_hB : 0≤B) (hR : 0≤R) :
    ∃ A D : ℝ, 0≤A ∧ 0≤D ∧ ∀ q : Coeff 2, ‖q‖≤B → ∀ E : ℂ, ‖E‖≤R →
      ‖hillEnergyDiscriminantGradientCurve q E‖≤A ∧
      ‖hillEnergyDiscriminantGradientSpatialCurve q E‖≤D := by
  let K : ℝ := (1+(R+1))^2*Real.exp ((R+1)+2*(1+B))
  have hK : 0<K := by dsimp only [K];positivity
  let D : ℝ := 8*K^3
  let A : ℝ := K+‖unitComplexCurvePrimitive‖*D
  have hD : 0≤D := by dsimp only [D];positivity
  refine ⟨A,D,by dsimp only [A];positivity,hD,?_⟩
  intro q hq E hE
  let z := Complex.sqrt E
  have hs : ‖z‖^2=‖E‖ := by rw [←norm_pow,complex_sqrt_sq]
  have hz : ‖z‖≤R+1 := by nlinarith [sq_nonneg (‖z‖-1)]
  have hstate (v : ℂ × ℂ) (hv : ‖v‖=1) : ‖hillL2FrequencyStateCurve q z v‖≤K := by
    apply (norm_hillL2FrequencyStateCurve_le q z v).trans
    rw [hv,mul_one]
    dsimp only [K]
    gcongr
  have hC := hstate (1,0) (by norm_num [Prod.norm_def])
  have hS := hstate (0,1) (by norm_num [Prod.norm_def])
  have hg := norm_hillDiscriminantGradientSpatialCurve_le_of_state_bounds q z K hK.le hC hS
  have hgrad := curve_eq_constant_add_unitComplexCurvePrimitive
    (hillDiscriminantGradientCurve q z) (hillDiscriminantGradientSpatialCurve q z)
    (absolutelyContinuousOnInterval_hillDiscriminantGradientCurve q z)
    (ae_hasDerivAt_hillDiscriminantGradientCurve q z)
  refine ⟨?_,hg⟩
  change ‖hillDiscriminantGradientCurve q z‖≤A
  rw [hgrad]
  have hzero : ‖hillDiscriminantGradientCurve q z ⟨0,by norm_num⟩‖≤K := by
    rw [(hillDiscriminantGradientCurve_endpoints q z).1]
    exact (norm_fst_le _).trans (((hillL2FrequencyStateCurve q z (0,1)).norm_coe_le_norm _).trans hS)
  apply (norm_add_le _ _).trans
  have hconst : ‖ContinuousMap.const (Icc (0 : ℝ) 1)
      (hillDiscriminantGradientCurve q z ⟨0,by norm_num⟩)‖≤K :=
    (ContinuousMap.norm_le _ hK.le).mpr (fun _ => hzero)
  exact (add_le_add hconst ((unitComplexCurvePrimitive.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left hg (norm_nonneg _))))

end NLS.KdV
