import NLS.MKdV.SobolevMiuraMagriCanonical
import NLS.Fourier.PeriodOneH2CurveData
import NLS.Poisson.UnitIntervalBilinearPairing

/-! # Identification of the native Magri bivector with its physical integral

The potential is only L². Both H² cotangents are constructed from actual
periodic interval curves. Parseval and periodic integration by parts give
the exact weak integral without differentiating the potential.
-/
noncomputable section
open Set Complex Filter Topology MeasureTheory
open NLS.FunctionalAnalysis NLS.LinearVolterra NLS.Fourier NLS.Poisson NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.MKdV

theorem periodOneSobolevProduct_coefficients_of_curves
    (a b : ScalarDomain 2) (f g : Curve ℂ)
    (ha : ∀ x ∈ Icc (0 : ℝ) 1, periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ)) = extend f x)
    (hb : ∀ x ∈ Icc (0 : ℝ) 1, periodOneSobolevSynthesis b (x : AddCircle (2 : ℝ)) = extend g x)
    (n : ℤ) :
    (periodOneSobolevProduct a b).val n = periodOneCoefficient (extend (f*g)) n := by
  rw [← periodOneCoefficient_periodOneSobolevSynthesis]
  apply congrFun (fourierCoeffOn_congr_ae (by norm_num : (0 : ℝ) < 1) ?_) n
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  rw [periodOneSobolevSynthesis_product,ha x ⟨hx.1.le,hx.2⟩,hb x ⟨hx.1.le,hx.2⟩]
  rfl

theorem reflectedHilbertPairing_product_eq_curve_integral
    (q : Coeff 2) (Q : ℝ → ℂ)
    (hQ : MemLp Q 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hq : ∀ n, q n = periodOneCoefficient Q n)
    (a b : ScalarDomain 2) (f g : Curve ℂ)
    (ha : ∀ x ∈ Icc (0 : ℝ) 1, periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ)) = extend f x)
    (hb : ∀ x ∈ Icc (0 : ℝ) 1, periodOneSobolevSynthesis b (x : AddCircle (2 : ℝ)) = extend g x) :
    reflectedHilbertPairing q (scalarInclusion (periodOneSobolevProduct a b)) =
      ∫ x in (0 : ℝ)..1,Q x*(extend f x*extend g x) := by
  exact reflectedHilbertPairing_eq_unit_integral q _ Q (extend (f*g)) hQ
    (memLp_unitCurve_extend 2 (f*g)) hq
    (fun n => by
      rw [scalarInclusion_apply]
      exact periodOneSobolevProduct_coefficients_of_curves a b f g ha hb n)

theorem hillSobolevMagriBivector_eq_curve_integral
    (q : Coeff 2) (Q : ℝ → ℂ)
    (hQ : MemLp Q 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hq : ∀ n, q n = periodOneCoefficient Q n)
    (D E : PeriodOneH2CurveData) :
    hillSobolevMagriBivector q D.native E.native =
      ∫ x in (0 : ℝ)..1,-D.second x*extend E.spatial x+
        2*Q x*(extend D.profile x*extend E.spatial x-extend D.spatial x*extend E.profile x) := by
  have hf : reflectedHilbertPairing (periodOneDerivative D.derivative) (scalarInclusion E.derivative) =
      ∫ x in (0 : ℝ)..1,D.second x*extend E.spatial x :=
    reflectedHilbertPairing_eq_unit_integral _ _ _ _ D.second_memLp
      (memLp_unitCurve_extend 2 E.spatial) D.second_apply (fun n => by rw [scalarInclusion_apply,E.derivative_apply])
  have hp := reflectedHilbertPairing_product_eq_curve_integral q Q hQ hq
    D.inclusion E.derivative D.profile E.spatial
    (fun _ hx => D.profile_recovery hx) (fun _ hx => E.spatial_recovery hx)
  have hr := reflectedHilbertPairing_product_eq_curve_integral q Q hQ hq
    D.derivative E.inclusion D.spatial E.profile
    (fun _ hx => D.spatial_recovery hx) (fun _ hx => E.profile_recovery hx)
  have hiQ : IntervalIntegrable Q volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr (hQ.integrable (by norm_num))
  have hiD : IntervalIntegrable D.second volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
      (D.second_memLp.integrable (by norm_num))
  have hi1 := hiD.mul_continuousOn (continuous_extend E.spatial).continuousOn
  have hi2 := hiQ.mul_continuousOn
    ((continuous_extend D.profile).mul (continuous_extend E.spatial)).continuousOn
  have hi3 := hiQ.mul_continuousOn
    ((continuous_extend D.spatial).mul (continuous_extend E.profile)).continuousOn
  change IntervalIntegrable (fun x => Q x*(extend D.profile x*extend E.spatial x)) volume 0 1 at hi2
  change IntervalIntegrable (fun x => Q x*(extend D.spatial x*extend E.profile x)) volume 0 1 at hi3
  change hillWeakMagriBivector q D.inclusion D.derivative E.inclusion E.derivative = _
  rw [hillWeakMagriBivector,reflectedHilbertPairing_periodOneDerivative,hf,map_sub,map_sub,hp,hr]
  have hin := hi1.neg
  have hiq := (hi2.sub hi3).const_mul 2
  rw [← intervalIntegral.integral_neg,← intervalIntegral.integral_sub hi2 hi3,
    ← intervalIntegral.integral_const_mul]
  refine (intervalIntegral.integral_add hin hiq).symm.trans ?_
  apply intervalIntegral.integral_congr
  intro x _
  simp only [Pi.neg_apply]
  ring

end NLS.MKdV
