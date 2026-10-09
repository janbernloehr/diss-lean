import NLS.ZakharovShabat.ClassicalRemainderBound
import NLS.FunctionalAnalysis.VariableForcingGronwall

/-! # The L2 forcing estimate toward Appendix G.1

Retain the actual time-dependent potential in the Duhamel inequality.
The resulting estimate has the literal A*exp(A) coefficient, where A is
an L2 potential budget, and the actual first Born term's L2 time norm.
These theorems apply to the constructed continuous-potential solution;
the extension to arbitrary L2 potentials is a separate requirement.
-/
noncomputable section
open Set Complex MeasureTheory
open NLS.LinearVolterra NLS.ComplexAnalysis NLS.FunctionalAnalysis
namespace NLS.ComplexAnalysis

/-- Continuity of the actual oscillatory integral in its terminal time. -/
theorem continuous_oscillatoryIntegral (c : ℂ) {f : ℝ → ℂ} (hf : Continuous f) :
    Continuous (fun t => oscillatoryIntegral c t f) := by
  have heq (t : ℝ) : oscillatoryIntegral c t f =
      exp (c*t)*(∫ s in (0:ℝ)..t, exp ((-2*c)*s)*f s) := by
    rw [oscillatoryIntegral,← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only [oscillatoryKernel]
    rw [← mul_assoc,← exp_add]
    congr 2
    push_cast
    ring
  simp_rw [heq]
  exact (show Continuous (fun t : ℝ => exp (c*t)) by fun_prop).mul
    (intervalIntegral.differentiable_integral_of_continuous
      (show Continuous (fun s : ℝ => exp ((-2*c)*s)*f s) by fun_prop)).continuous

end NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

/-- The first Born term is continuous without differentiating the potential. -/
theorem continuous_classicalFirstBornVector (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) :
    Continuous (classicalFirstBornVector φ z v) := by
  exact ((continuous_const.mul (continuous_oscillatoryIntegral (-I*z) (continuous_extend φ).fst)).mul
    continuous_const).prodMk
    ((continuous_const.mul (continuous_oscillatoryIntegral (I*z) (continuous_extend φ).snd)).mul
      continuous_const)

/-- The first Born term with the same exponential weight as the full remainder. -/
def classicalNormalizedFirstBorn (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) (t : ℝ) : ℝ :=
  Real.exp (-(|z.im| * t))*‖classicalFirstBornVector φ z v t‖

theorem continuous_classicalNormalizedFirstBorn (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) :
    Continuous (classicalNormalizedFirstBorn φ z v) :=
  (show Continuous (fun t : ℝ => Real.exp (-(|z.im| * t))) by fun_prop).mul
    (continuous_classicalFirstBornVector φ z v).norm

/-- The Hilbert L2 norm of both potential coordinates on the unit interval,
written as a literal square integral; it is not the curve supremum norm. -/
def classicalPotentialL2Norm (φ : Curve (ℂ × ℂ)) : ℝ :=
  Real.sqrt (∫ s in (0:ℝ)..1, ‖(extend φ s).1‖^2+‖(extend φ s).2‖^2)

/-- The local L2 norm of the pointwise product norm is bounded by the
Hilbert L2 norm of the potential on the whole interval. -/
theorem sqrt_integral_potential_norm_sq_le (φ : Curve (ℂ × ℂ)) (t : Icc (0:ℝ) 1) :
    Real.sqrt (∫ s in (0:ℝ)..t.val, ‖extend φ s‖^2) ≤ classicalPotentialL2Norm φ := by
  apply Real.sqrt_le_sqrt
  have hc : Continuous (fun s => ‖(extend φ s).1‖^2+‖(extend φ s).2‖^2) :=
    ((continuous_extend φ).fst.norm.pow 2).add ((continuous_extend φ).snd.norm.pow 2)
  apply (intervalIntegral.integral_mono_on t.property.1
    (((continuous_extend φ).norm.pow 2).intervalIntegrable 0 t)
    (hc.intervalIntegrable 0 t) (fun s _ => ?_)).trans
    (intervalIntegral.integral_mono_interval le_rfl t.property.1 t.property.2
      (Filter.Eventually.of_forall (fun s => add_nonneg (sq_nonneg _) (sq_nonneg _)))
      (hc.intervalIntegrable 0 1))
  change ‖extend φ s‖^2 ≤ _
  rw [Prod.norm_def]
  rcases le_total ‖(extend φ s).1‖ ‖(extend φ s).2‖ with h | h
  · rw [max_eq_right h]
    exact le_add_of_nonneg_left (sq_nonneg _)
  · rw [max_eq_left h]
    exact le_add_of_nonneg_right (sq_nonneg _)


/-- The pointwise potential norm, rather than its supremum, controls the
actual normalized remainder's Volterra term. -/
theorem classicalNormalizedRemainder_le_firstBorn_add_variable_integral
    (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    classicalNormalizedRemainder φ z v t ≤
      Real.exp (-(|z.im| * t.val))*‖classicalFirstBornVector φ z v t‖+
        (∫ s in (0 : ℝ)..t.val, ‖extend φ s‖*classicalNormalizedRemainder φ z v s) := by
  let R := classicalSolutionRemainder φ z v
  let E := Real.exp (-(|z.im| * t.val))
  have hE : 0 ≤ E := Real.exp_nonneg _
  have hr : Continuous (fun s : ℝ => ‖extend φ s‖*‖R s‖) :=
    (continuous_extend φ).norm.mul (continuous_classicalSolutionRemainder φ z v).norm
  have hfst : E*‖∫ s in (0 : ℝ)..t.val, exp (-I*z*(t.val-s))*(I*(extend φ s).1*(R s).2)‖ ≤
      (∫ s in (0 : ℝ)..t.val, ‖extend φ s‖*classicalNormalizedRemainder φ z v s) := by
    have h := norm_exp_integral_weighted_le (-I*z) |z.im| t
      (by simpa [Complex.mul_re] using le_abs_self z.im) t.property.1
      (fun s => I*(extend φ s).1*(R s).2) (fun s => ‖extend φ s‖*‖R s‖) hr (by
        intro s _
        simp only [norm_mul,norm_I,one_mul]
        exact mul_le_mul (norm_fst_le (extend φ s))
          (norm_snd_le (R s)) (norm_nonneg _) (norm_nonneg _))
    have he : (fun s : ℝ => Real.exp (-|z.im| * s)*(‖extend φ s‖*‖R s‖)) =
        fun s => ‖extend φ s‖*classicalNormalizedRemainder φ z v s := by
      funext s
      dsimp only [classicalNormalizedRemainder,R]
      rw [neg_mul]
      ring
    rw [he] at h
    simpa only [Complex.ofReal_sub,neg_mul] using h
  have hsnd : E*‖∫ s in (0 : ℝ)..t.val, exp (I*z*(t.val-s))*((-I)*(extend φ s).2*(R s).1)‖ ≤
      (∫ s in (0 : ℝ)..t.val, ‖extend φ s‖*classicalNormalizedRemainder φ z v s) := by
    have h := norm_exp_integral_weighted_le (I*z) |z.im| t
      (by simpa [Complex.mul_re] using neg_le_abs z.im) t.property.1
      (fun s => (-I)*(extend φ s).2*(R s).1) (fun s => ‖extend φ s‖*‖R s‖) hr (by
        intro s _
        simp only [norm_mul,norm_neg,norm_I,one_mul]
        exact mul_le_mul (norm_snd_le (extend φ s))
          (norm_fst_le (R s)) (norm_nonneg _) (norm_nonneg _))
    have he : (fun s : ℝ => Real.exp (-|z.im| * s)*(‖extend φ s‖*‖R s‖)) =
        fun s => ‖extend φ s‖*classicalNormalizedRemainder φ z v s := by
      funext s
      dsimp only [classicalNormalizedRemainder,R]
      rw [neg_mul]
      ring
    rw [he] at h
    simpa only [Complex.ofReal_sub,neg_mul] using h
  change E*‖R t‖ ≤ _
  rw [Prod.norm_def,mul_max_of_nonneg _ _ hE]
  apply max_le
  · change E*‖(classicalSolutionRemainder φ z v t).1‖ ≤ _
    rw [classicalSolutionRemainder_fst_duhamel]
    exact (mul_le_mul_of_nonneg_left (norm_add_le _ _) hE).trans
      (by
        rw [mul_add]
        exact add_le_add (mul_le_mul_of_nonneg_left (norm_fst_le _) hE) hfst)
  · change E*‖(classicalSolutionRemainder φ z v t).2‖ ≤ _
    rw [classicalSolutionRemainder_snd_duhamel]
    exact (mul_le_mul_of_nonneg_left (norm_add_le _ _) hE).trans
      (by
        rw [mul_add]
        exact add_le_add (mul_le_mul_of_nonneg_left (norm_snd_le _) hE) hsnd)


/-- The literal G.1 coefficient and time-L2 forcing norm for every initial
vector of the actual continuous-potential fundamental solution. No smoothness,
nonzero-frequency, or small-potential hypothesis is imposed. -/
theorem classicalNormalizedRemainder_le_L2_firstBorn
    (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) (t : Icc (0:ℝ) 1) :
    classicalNormalizedRemainder φ z v t ≤ classicalNormalizedFirstBorn φ z v t +
      classicalPotentialL2Norm φ*Real.exp (classicalPotentialL2Norm φ)*
        Real.sqrt (∫ s in (0:ℝ)..t.val, (classicalNormalizedFirstBorn φ z v s)^2) := by
  apply le_forcing_add_L2_bound (classicalNormalizedRemainder φ z v)
    (classicalNormalizedFirstBorn φ z v) (fun s => ‖extend φ s‖)
    (continuous_classicalNormalizedRemainder φ z v)
    (continuous_classicalNormalizedFirstBorn φ z v) (continuous_extend φ).norm
    t (classicalPotentialL2Norm φ) t.property
    (fun s _ => norm_nonneg _) (fun s _ => mul_nonneg (Real.exp_nonneg _) (norm_nonneg _))
    (sqrt_integral_potential_norm_sq_le φ t)
  intro s hs
  exact classicalNormalizedRemainder_le_firstBorn_add_variable_integral φ z v
    ⟨s,hs.1,hs.2.trans t.property.2⟩

end NLS.ZakharovShabat
