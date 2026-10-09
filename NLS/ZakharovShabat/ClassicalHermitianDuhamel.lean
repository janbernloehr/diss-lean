import NLS.ComplexAnalysis.HermitianPair
import NLS.ZakharovShabat.ClassicalRemainderL2Bound

/-! # Duhamel estimates in the actual Hermitian vector norm

The signed coordinate equations are transported through a continuous linear
equivalence. The subsequent norm estimates are proved directly in the
Euclidean norm, so the potential coefficient has no conversion factor.
-/
noncomputable section
open Set Complex MeasureTheory
open NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

/-- The full error vector with its Hermitian norm and the source exponential weight. -/
def classicalHermitianRemainder (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) (t : ℝ) : ℝ :=
  Real.exp (-(|z.im| * t))*‖hermitianPair (classicalSolutionRemainder φ z v t)‖

/-- The actual first Born vector in the identical weighted Hermitian norm. -/
def classicalHermitianFirstBorn (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) (t : ℝ) : ℝ :=
  Real.exp (-(|z.im| * t))*‖hermitianPair (classicalFirstBornVector φ z v t)‖

theorem continuous_classicalHermitianRemainder (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) :
    Continuous (classicalHermitianRemainder φ z v) :=
  (show Continuous (fun t : ℝ => Real.exp (-(|z.im| * t))) by fun_prop).mul
    (hermitianPairEquiv.symm.continuous.comp (continuous_classicalSolutionRemainder φ z v)).norm

theorem continuous_classicalHermitianFirstBorn (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) :
    Continuous (classicalHermitianFirstBorn φ z v) :=
  (show Continuous (fun t : ℝ => Real.exp (-(|z.im| * t))) by fun_prop).mul
    (hermitianPairEquiv.symm.continuous.comp (continuous_classicalFirstBornVector φ z v)).norm

/-- The signed free propagator and off-diagonal potential acting on an error vector. -/
def classicalHermitianDuhamelKernel (z : ℂ) (r : ℝ) (φ v : ℂ × ℂ) : HermitianPair :=
  hermitianPair (exp (-I*z*r)*(I*φ.1*v.2),exp (I*z*r)*((-I)*φ.2*v.1))

/-- Sharp coefficient one for the kernel in the Hermitian norm. -/
theorem norm_classicalHermitianDuhamelKernel_le (z : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (φ v : ℂ × ℂ) :
    ‖classicalHermitianDuhamelKernel z r φ v‖ ≤
      Real.exp (|z.im| * r)*‖φ‖*‖hermitianPair v‖ := by
  have hExp (c : ℂ) (hc : c.re ≤ |z.im|) : ‖exp (c*r)‖ ≤ Real.exp (|z.im| * r) := by
    rw [norm_exp]
    apply Real.exp_le_exp.mpr
    simpa only [mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero] using mul_le_mul_of_nonneg_right hc hr
  have h₁ := hExp (-I*z) (by simpa [mul_re] using le_abs_self z.im)
  have h₂ := hExp (I*z) (by simpa [mul_re] using neg_le_abs z.im)
  have hφ := hermitianPair_norm_diagonal_le (I*φ.1) ((-I)*φ.2) (v.2,v.1) ‖φ‖
    (norm_nonneg _) (by simpa using norm_fst_le φ) (by simpa using norm_snd_le φ)
  rw [hermitianPair_norm_swap] at hφ
  exact (hermitianPair_norm_diagonal_le (exp (-I*z*r)) (exp (I*z*r))
    (I*φ.1*v.2,(-I)*φ.2*v.1) (Real.exp (|z.im| * r)) (Real.exp_nonneg _) h₁ h₂).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hφ (Real.exp_nonneg (|z.im| * r)))

/-- The actual two coordinate equations form a single Hermitian-valued integral identity. -/
theorem classicalHermitianRemainder_duhamel (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ)
    (t : Icc (0:ℝ) 1) :
    hermitianPair (classicalSolutionRemainder φ z v t) =
      hermitianPair (classicalFirstBornVector φ z v t) +
        ∫ s in (0:ℝ)..t.val, classicalHermitianDuhamelKernel z (t.val-s)
          (extend φ s) (classicalSolutionRemainder φ z v s) := by
  let k (s : ℝ) : ℂ × ℂ :=
    (exp (-I*z*(t.val-s))*(I*(extend φ s).1*(classicalSolutionRemainder φ z v s).2),
      exp (I*z*(t.val-s))*((-I)*(extend φ s).2*(classicalSolutionRemainder φ z v s).1))
  have hkc : Continuous k := by
    have hφ := continuous_extend φ
    have hR := continuous_classicalSolutionRemainder φ z v
    exact ((show Continuous (fun s : ℝ => exp (-I*z*(t.val-s))) by fun_prop).mul
      ((continuous_const.mul hφ.fst).mul hR.snd)).prodMk
      ((show Continuous (fun s : ℝ => exp (I*z*(t.val-s))) by fun_prop).mul
        ((continuous_const.mul hφ.snd).mul hR.fst))
  have heq : classicalSolutionRemainder φ z v t =
      classicalFirstBornVector φ z v t+∫ s in (0:ℝ)..t.val, k s := by
    apply Prod.ext
    · have hi := (ContinuousLinearMap.fst ℂ ℂ ℂ).intervalIntegral_comp_comm (hkc.intervalIntegrable (μ := volume) 0 t)
      simpa only [ContinuousLinearMap.coe_fst',Prod.fst_add] using
        (classicalSolutionRemainder_fst_duhamel φ z v t).trans (congrArg
          (fun x => (classicalFirstBornVector φ z v t).1+x) hi)
    · have hi := (ContinuousLinearMap.snd ℂ ℂ ℂ).intervalIntegral_comp_comm (hkc.intervalIntegrable (μ := volume) 0 t)
      simpa only [ContinuousLinearMap.coe_snd',Prod.snd_add] using
        (classicalSolutionRemainder_snd_duhamel φ z v t).trans (congrArg
          (fun x => (classicalFirstBornVector φ z v t).2+x) hi)
  rw [heq]
  change hermitianPairEquiv.symm (_+_) = _
  rw [map_add]
  apply congrArg (fun x => hermitianPair (classicalFirstBornVector φ z v t)+x)
  simpa only [classicalHermitianDuhamelKernel,hermitianPair,k,ofReal_sub,ContinuousLinearEquiv.coe_coe] using
    (hermitianPairEquiv.symm.toContinuousLinearMap.intervalIntegral_comp_comm
      (hkc.intervalIntegrable (μ := volume) 0 t)).symm

/-- The normalized Duhamel inequality with its original pointwise potential
coefficient is valid in the Hermitian norm, without a sqrt(2) loss. -/
theorem classicalHermitianRemainder_le_firstBorn_add_integral
    (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) (t : Icc (0:ℝ) 1) :
    classicalHermitianRemainder φ z v t ≤ classicalHermitianFirstBorn φ z v t +
      ∫ s in (0:ℝ)..t.val, ‖extend φ s‖*classicalHermitianRemainder φ z v s := by
  let E := Real.exp (-(|z.im| * t.val))
  have hmajor : ‖∫ s in (0:ℝ)..t.val, classicalHermitianDuhamelKernel z (t.val-s)
        (extend φ s) (classicalSolutionRemainder φ z v s)‖ ≤
      ∫ s in (0:ℝ)..t.val, Real.exp (|z.im| * (t.val-s))*‖extend φ s‖*
        ‖hermitianPair (classicalSolutionRemainder φ z v s)‖ := by
    apply intervalIntegral.norm_integral_le_of_norm_le t.property.1
    · filter_upwards [] with s hs
      exact norm_classicalHermitianDuhamelKernel_le z (t.val-s) (sub_nonneg.mpr hs.2) _ _
    · have hφ := continuous_extend φ
      have hR := hermitianPairEquiv.symm.continuous.comp (continuous_classicalSolutionRemainder φ z v)
      exact (((show Continuous (fun s : ℝ => Real.exp (|z.im| * (t.val-s))) by fun_prop).mul
        hφ.norm).mul hR.norm).intervalIntegrable 0 t
  have hnorm := mul_le_mul_of_nonneg_left hmajor (Real.exp_nonneg (-(|z.im| * t.val)))
  have heq : E*(∫ s in (0:ℝ)..t.val, Real.exp (|z.im| * (t.val-s))*‖extend φ s‖*
        ‖hermitianPair (classicalSolutionRemainder φ z v s)‖) =
      ∫ s in (0:ℝ)..t.val, ‖extend φ s‖*classicalHermitianRemainder φ z v s := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    dsimp [E,classicalHermitianRemainder]
    rw [← mul_assoc,← mul_assoc,← Real.exp_add]
    rw [show -(|z.im| * t.val)+|z.im| * (t.val-s) = -(|z.im| * s) by ring]
    ring
  change E*_ ≤ E*_+_
  rw [classicalHermitianRemainder_duhamel]
  exact (mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.exp_nonneg _)).trans
    (by rw [mul_add]; exact add_le_add (le_refl _) (hnorm.trans_eq heq))

end NLS.ZakharovShabat
