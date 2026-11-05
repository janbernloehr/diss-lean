import NLS.KdV.HillHminusOneIntrinsicWeakForm
import NLS.FunctionalAnalysis.IntervalH1Conjugation
import NLS.SequenceSpaces.PeriodOneHminusOneRealDensity

/-! # Reality of the intrinsic weak Hill quadratic form

Conjugate-reflected Fourier coefficients give an actually real physical
L2 class. The ordinary integral form is real on a curve and its conjugate.
Real L2 density and norm continuity transfer that identity to all real
H^-1 potentials, without selecting a real Riccati lift.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open scoped ComplexConjugate
open NLS.LinearVolterra NLS.Fourier NLS.ZakharovShabat NLS.MKdV NLS.FunctionalAnalysis
namespace NLS.KdV

theorem unitL2Synthesis_star_eq_self_of_real (p : Coeff 2)
    (hp : ∀ k : ℤ, p (-k) = conj (p k)) :
    star (unitL2SynthesisEquiv p) = unitL2SynthesisEquiv p := by
  apply unitL2_ext_coefficients
  intro n
  have hc (k : ℤ) : intervalFourierCoefficient 1 (unitL2SynthesisEquiv p) k = p k :=
    unitL2SynthesisLinear_coefficient p k
  rw [intervalFourierCoefficient_Lp_star,hc,hc,hp]
  exact conj_conj _

theorem physicalL2HillWeakForm_star_self (b : IntervalL2) (hb : star b = b) (y : Curve ℂ) :
    conj (physicalL2HillWeakForm b y (star y)) = physicalL2HillWeakForm b y (star y) := by
  have hbAE : (fun s => conj (b s)) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] b := by
    have he := Lp.coeFn_star b
    rw [hb] at he
    exact he.symm
  simp only [physicalL2HillWeakForm,physicalL2HillPotentialPairing_apply,
    deriv_extend_curve_star,map_add]
  congr 1
  · rw [← intervalIntegral.intervalIntegral_conj]
    apply intervalIntegral.integral_congr
    intro s _
    simp only [map_mul,conj_conj]
    ring
  · rw [← intervalIntegral.intervalIntegral_conj]
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    filter_upwards [hbAE] with s hs
    change conj (b s*(NLS.LinearVolterra.extend y s*conj (NLS.LinearVolterra.extend y s))) =
      b s*(NLS.LinearVolterra.extend y s*conj (NLS.LinearVolterra.extend y s))
    simp only [map_mul,conj_conj,hs]
    ring

/-- All real H^-1 inputs are covered, including nonzero mean. Only the
product endpoint condition needed by the intrinsic form is imposed. -/
theorem hillHminusWeakForm_star_self (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (y : Curve ℂ) (hy : AbsolutelyContinuousOnInterval (extend y) 0 1)
    (hy₂ : MemLp (deriv (extend y)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hend : extend y 1*conj (extend y 1) = extend y 0*conj (extend y 0)) :
    conj (hillHminusWeakForm q y (star y)) = hillHminusWeakForm q y (star y) := by
  have hys := absolutelyContinuous_curve_star y hy
  have hys₂ := memLp_deriv_curve_star y hy₂
  have ha := analyticOnNhd_hillHminusWeakForm y (star y) hy hys hy₂ hys₂ hend
  have hc : Continuous (fun p : PeriodOneRealHminusOne => hillHminusWeakForm p.val y (star y)) :=
    ha.continuous.comp continuous_subtype_val
  have he := denseRange_periodOneRealL2Inclusion.equalizer
    (Complex.continuous_conj.comp hc) hc (by
      funext p
      change conj (hillHminusWeakForm (periodOneL2Inclusion p.val) y (star y)) =
        hillHminusWeakForm (periodOneL2Inclusion p.val) y (star y)
      rw [hillHminusWeakForm_eq_physicalL2 p.val y (star y) hy hys hy₂ hys₂ hend]
      exact physicalL2HillWeakForm_star_self _ (unitL2Synthesis_star_eq_self_of_real p.val p.property) y)
  exact congrFun he (⟨q,hr⟩ : PeriodOneRealHminusOne)

theorem physicalL2HillWeakForm_conj (b : IntervalL2) (hb : star b = b) (y φ : Curve ℂ) :
    conj (physicalL2HillWeakForm b y φ) = physicalL2HillWeakForm b (star y) (star φ) := by
  have hbAE : (fun s => conj (b s)) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] b := by
    have he := Lp.coeFn_star b
    rw [hb] at he
    exact he.symm
  simp only [physicalL2HillWeakForm,physicalL2HillPotentialPairing_apply,
    deriv_extend_curve_star,map_add]
  congr 1
  · rw [← intervalIntegral.intervalIntegral_conj]
    apply intervalIntegral.integral_congr
    intro s _
    exact map_mul _ _ _
  · rw [← intervalIntegral.intervalIntegral_conj]
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    filter_upwards [hbAE] with s hs
    change conj (b s*(NLS.LinearVolterra.extend y s*NLS.LinearVolterra.extend φ s)) =
      b s*(conj (NLS.LinearVolterra.extend y s)*conj (NLS.LinearVolterra.extend φ s))
    rw [map_mul,map_mul,hs]

/-- Conjugation symmetry on every admissible H1 curve pair follows in
original H^-1 from the actual real L2 potential pairing. -/
theorem hillHminusWeakForm_conj (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (y φ : Curve ℂ) (hy : AbsolutelyContinuousOnInterval (extend y) 0 1)
    (hφ : AbsolutelyContinuousOnInterval (extend φ) 0 1)
    (hy₂ : MemLp (deriv (extend y)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hφ₂ : MemLp (deriv (extend φ)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hend : extend y 1*extend φ 1 = extend y 0*extend φ 0) :
    conj (hillHminusWeakForm q y φ) = hillHminusWeakForm q (star y) (star φ) := by
  have hys := absolutelyContinuous_curve_star y hy
  have hφs := absolutelyContinuous_curve_star φ hφ
  have hys₂ := memLp_deriv_curve_star y hy₂
  have hφs₂ := memLp_deriv_curve_star φ hφ₂
  have hends : extend (star y) 1*extend (star φ) 1 = extend (star y) 0*extend (star φ) 0 := by
    simpa only [NLS.LinearVolterra.extend,ContinuousMap.star_apply,Complex.star_def,map_mul]
      using congrArg (starRingEnd ℂ) hend
  have hc : Continuous (fun p : PeriodOneRealHminusOne => hillHminusWeakForm p.val y φ) :=
    (analyticOnNhd_hillHminusWeakForm y φ hy hφ hy₂ hφ₂ hend).continuous.comp continuous_subtype_val
  have hcs : Continuous (fun p : PeriodOneRealHminusOne => hillHminusWeakForm p.val (star y) (star φ)) :=
    (analyticOnNhd_hillHminusWeakForm (star y) (star φ) hys hφs hys₂ hφs₂ hends).continuous.comp continuous_subtype_val
  have he := denseRange_periodOneRealL2Inclusion.equalizer (Complex.continuous_conj.comp hc) hcs (by
    funext p
    change conj (hillHminusWeakForm (periodOneL2Inclusion p.val) y φ) =
      hillHminusWeakForm (periodOneL2Inclusion p.val) (star y) (star φ)
    rw [hillHminusWeakForm_eq_physicalL2 p.val y φ hy hφ hy₂ hφ₂ hend,
      hillHminusWeakForm_eq_physicalL2 p.val (star y) (star φ) hys hφs hys₂ hφs₂ hends]
    exact physicalL2HillWeakForm_conj _ (unitL2Synthesis_star_eq_self_of_real p.val p.property) y φ)
  exact congrFun he (⟨q,hr⟩ : PeriodOneRealHminusOne)

end NLS.KdV
