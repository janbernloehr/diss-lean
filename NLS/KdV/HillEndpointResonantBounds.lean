import NLS.KdV.HillFreeModeProjection
import NLS.KdV.PseudomeasureInhomogeneousReduction

/-! Original physical L2 control of all raw H1 Fourier coefficients,
every shifted endpoint norm, and the literal two-mode amplitudes. -/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

/-- Every original raw Fourier coefficient has physical L2 bound ONE. -/
theorem norm_hillH1_coefficient_le_L2 (f : FourierLebesgueSpace (2:ℝ) 1 2) (k : ℤ) :
    ‖f.val (mode (-k))‖ ≤ ‖singularHillL2DomainInclusion f‖ := by
  have h := lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞) ≠ 0) (h1L2Coefficients f) k
  rw [h1L2Coefficients_apply] at h
  exact h.trans_eq (norm_singularHillL2DomainInclusion f).symm

/-- Every shifted negative endpoint norm is controlled by the SAME original
physical L2 norm. No frequency-dependent constant is lost. -/
theorem negativeShiftedNorm_H1EndpointInclusion_le_L2 (r : ℝ) (hr : 0 ≤ r)
    (f : FourierLebesgueSpace (2:ℝ) 1 2) (i : ℤ) :
    SpectralWeight.one.negativeShiftedNorm r hr i ⊤ (H1EndpointInclusion r hr f) ≤
      ‖singularHillL2DomainInclusion f‖ := by
  change ‖WeightedCoeff.weightEquiv ((SpectralWeight.one.negativeSobolev r).shift i) ⊤
    (SpectralWeight.one.negativeShiftEquiv r hr i ⊤ (H1EndpointInclusion r hr f))‖ ≤ _
  apply lp.norm_le_of_forall_le (norm_nonneg _)
  intro k
  rw [WeightedCoeff.weightEquiv_apply,SpectralWeight.negativeShiftEquiv_apply,H1EndpointInclusion_apply]
  simp only [Weight.shift_apply,norm_mul,Complex.norm_real,Real.norm_of_nonneg
    ((SpectralWeight.one.negativeSobolev r).positive (k+i)).le]
  have hw : SpectralWeight.one.negativeSobolev r (k+i) ≤ 1 := by
    simp only [SpectralWeight.negativeSobolev_eq_product,SpectralWeight.one_apply,one_mul]
    have h := Weight.sobolev_mono (show -r ≤ 0 by linarith) (k+i)
    simpa only [Weight.sobolev_apply,Real.rpow_zero] using h
  exact (mul_le_mul_of_nonneg_right hw (norm_nonneg _)).trans
    (by simpa only [one_mul] using norm_hillH1_coefficient_le_L2 f k)

/-- Both original resonant amplitudes have max-norm at most the physical L2 norm. -/
theorem norm_endpointHillH1Coordinates_le_L2 (n : ℕ) (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    ‖endpointHillH1Coordinates n f‖ ≤ ‖singularHillL2DomainInclusion f‖ := by
  rw [endpointHillH1Coordinates_apply,Prod.norm_def]
  exact max_le (norm_hillH1_coefficient_le_L2 f n)
    (by simpa only [neg_neg] using norm_hillH1_coefficient_le_L2 f (-(n:ℤ)))

/-- The literal free physical projector is controlled by TWICE the actual
max-norm of the original resonant amplitudes. -/
theorem norm_hillFreeL2ModeProjection_le_two_coordinates (n : ℕ)
    (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    ‖hillFreeL2ModeProjection n (singularHillL2DomainInclusion f)‖ ≤ 2*‖endpointHillH1Coordinates n f‖ := by
  change ‖circleContinuousToLp 2 (hillFreeContinuousModeProjection n (singularHillL2DomainInclusion f))‖ ≤ _
  apply (norm_circleContinuousToLp_le 2 _).trans
  rw [hillFreeContinuousModeProjection_apply]
  have hb := norm_add_le
    (fourierCoeff (singularHillL2DomainInclusion f) (n:ℤ) • (fourier (n:ℤ) : C(AddCircle (2:ℝ),ℂ)))
    (fourierCoeff (singularHillL2DomainInclusion f) (-(n:ℤ)) • (fourier (-(n:ℤ)) : C(AddCircle (2:ℝ),ℂ)))
  rw [norm_smul,norm_smul,fourier_norm,fourier_norm,mul_one,mul_one,
    singularHillL2DomainInclusion_coefficient,singularHillL2DomainInclusion_coefficient,neg_neg] at hb
  rw [singularHillL2DomainInclusion_coefficient,singularHillL2DomainInclusion_coefficient,neg_neg]
  apply hb.trans
  rw [endpointHillH1Coordinates_apply,Prod.norm_def]
  nlinarith [le_max_left ‖f.val (mode (-(n:ℤ)))‖ ‖f.val (mode (n:ℤ))‖,
    le_max_right ‖f.val (mode (-(n:ℤ)))‖ ‖f.val (mode (n:ℤ))‖]

end NLS.KdV
