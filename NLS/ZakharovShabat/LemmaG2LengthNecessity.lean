import NLS.ZakharovShabat.LemmaG2IntegralNormAudit

/-! # The short-interval growth required by the integral norm in G.2

Constant smooth periodic potentials at frequency pi/(2t) force the numerator
of any bound B(t)/(2|z|) to be at least 2/sqrt(t).
-/
noncomputable section
open Set MeasureTheory
open NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

/-- The exact local integral norm of the constant test potential at every length. -/
theorem g2IntegralNormTestPotential_norm_length (t : ℝ) (ht : 0 ≤ t) :
    intervalPairH1Norm g2IntegralNormTestPotential t = Real.sqrt t := by
  simp [intervalPairH1Norm,intervalH1Norm,g2IntegralNormTestPotential,Real.sq_sqrt ht]

/-- A half-phase oscillatory integral, at an arbitrary positive interval length. -/
theorem oscillatoryIntegral_const_half_phase (t : ℝ) (ht : 0 < t) :
    oscillatoryIntegral (Complex.I*((Real.pi/(2*t) : ℝ) : ℂ)) t (fun _ => (1 : ℂ)) =
      ((2*t/Real.pi : ℝ) : ℂ) := by
  have hc : Complex.I*((Real.pi/(2*t) : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity)))
  rw [oscillatoryIntegral_const _ hc]
  have hp : (Complex.I*((Real.pi/(2*t) : ℝ) : ℂ))*(t : ℂ) = (Real.pi : ℂ)/2*Complex.I := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr ht.ne']
  have hm : -(Complex.I*((Real.pi/(2*t) : ℝ) : ℂ))*(t : ℂ) = -(Real.pi : ℂ)/2*Complex.I := by
    rw [neg_mul,hp]
    ring
  rw [hp,hm,Complex.exp_pi_div_two_mul_I,Complex.exp_neg_pi_div_two_mul_I]
  push_cast
  field_simp
  ring

/-- Exact first Born norm at a length-dependent nonzero real frequency. -/
theorem g2IntegralNormTestPotential_firstBorn_length (t : ℝ) (ht : 0 < t) :
    Real.exp (-(|((Real.pi/(2*t) : ℝ) : ℂ).im| * t))*
      ‖intervalHermitianFirstBornOperator g2IntegralNormTestPotential (Real.pi/(2*t) : ℝ) t‖ =
      2*t/Real.pi := by
  simp only [Complex.ofReal_im,abs_zero,zero_mul,neg_zero,Real.exp_zero,one_mul]
  have hc : Complex.I*((Real.pi/(2*t) : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity)))
  rw [norm_intervalHermitianFirstBornOperator]
  dsimp only [g2IntegralNormTestPotential]
  rw [neg_mul,oscillatoryIntegral_neg_const _ hc,oscillatoryIntegral_const_half_phase t ht]
  simp [oscillatoryIntegral,Real.norm_eq_abs,abs_of_pos ht,abs_of_pos Real.pi_pos]
  positivity

/-- Any integral-norm bound of the printed form requires at least 2/sqrt(t)
in its numerator. In particular, a bounded numerator near zero is impossible. -/
theorem lemmaG2_integralNorm_length_necessary (t : ℝ) (ht : 0 < t) (B : ℝ)
    (h : Real.exp (-(|((Real.pi/(2*t) : ℝ) : ℂ).im| * t))*
      ‖intervalHermitianFirstBornOperator g2IntegralNormTestPotential (Real.pi/(2*t) : ℝ) t‖ ≤
        B/(2*‖((Real.pi/(2*t) : ℝ) : ℂ)‖)*intervalPairH1Norm g2IntegralNormTestPotential t) :
    2/Real.sqrt t ≤ B := by
  rw [g2IntegralNormTestPotential_firstBorn_length t ht,g2IntegralNormTestPotential_norm_length t ht.le] at h
  have hz : 0 < Real.pi/(2*t) := by positivity
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hz] at h
  have he : 2*t/Real.pi = 2/(2*(Real.pi/(2*t))) := by field_simp
  rw [he,div_mul_eq_mul_div] at h
  have hh := (div_le_div_iff_of_pos_right (show 0 < 2*(Real.pi/(2*t)) by positivity)).mp h
  exact (div_le_iff₀ (Real.sqrt_pos.mpr ht)).mpr (by simpa only [mul_comm] using hh)

/-- No fixed numerator can bound all short intervals, even for this one
smooth period-one potential and real nonzero frequencies. -/
theorem lemmaG2_integralNorm_no_uniform_numerator :
    ¬ ∃ B : ℝ, ∀ t : ℝ, 0 < t →
      Real.exp (-(|((Real.pi/(2*t) : ℝ) : ℂ).im| * t))*
        ‖intervalHermitianFirstBornOperator g2IntegralNormTestPotential (Real.pi/(2*t) : ℝ) t‖ ≤
          B/(2*‖((Real.pi/(2*t) : ℝ) : ℂ)‖)*intervalPairH1Norm g2IntegralNormTestPotential t := by
  rintro ⟨B,hB⟩
  let t := (|B|+1)⁻¹^2
  have ha : 0 < |B|+1 := by positivity
  have ht : 0 < t := by dsimp [t]; positivity
  have hh := lemmaG2_integralNorm_length_necessary t ht B (hB t ht)
  have hr : Real.sqrt t = (|B|+1)⁻¹ := by
    exact Real.sqrt_sq (by positivity)
  rw [hr,div_inv_eq_mul] at hh
  linarith [le_abs_self B]

end NLS.ZakharovShabat
