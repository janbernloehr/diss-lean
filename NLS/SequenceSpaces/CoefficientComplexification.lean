import NLS.SequenceSpaces.RealCoeff
import Mathlib.Tactic.Module

/-! # Complexification of continuous real-linear coefficient maps

Real and imaginary projections are contractions. Extending a real-linear map
by `f(Re z) + I • f(Im z)` gives a complex-linear map with norm at most twice
the original norm, and recovers the original map on every real sequence.
-/
noncomputable section
open scoped ENNReal
namespace NLS.Coeff.Complexification
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Imaginary coefficients as a continuous real-linear map. -/
def imCLM (p : ℝ≥0∞) [Fact (1 ≤ p)] : Coeff p →L[ℝ] RealCoeff p :=
  lp.mapCLM p (fun _ => Complex.imCLM) (norm_nonneg _) (fun _ => le_rfl)

@[simp] theorem imCLM_apply (a : Coeff p) (n : ℤ) : imCLM p a n = (a n).im := rfl

/-- Real coefficients of a complex scalar product. -/
lemma re_smul (z : ℂ) (a : Coeff p) :
    Coeff.reCLM p (z • a) = z.re • Coeff.reCLM p a-z.im • imCLM p a := by
  ext n
  change (z*a n).re = z.re*(a n).re-z.im*(a n).im
  exact Complex.mul_re z (a n)

/-- Imaginary coefficients of a complex scalar product. -/
lemma im_smul (z : ℂ) (a : Coeff p) :
    imCLM p (z • a) = z.re • imCLM p a+z.im • Coeff.reCLM p a := by
  ext n
  change (z*a n).im = z.re*(a n).im+z.im*(a n).re
  exact Complex.mul_im z (a n)

/-- Real projection is a contraction, also at the infinite exponent. -/
lemma norm_re_le (a : Coeff p) : ‖Coeff.reCLM p a‖ ≤ ‖a‖ := by
  apply lp.norm_mono (ne_of_gt (zero_lt_one.trans_le Fact.out))
  intro n
  exact Complex.abs_re_le_norm (a n)

/-- Imaginary projection is a contraction. -/
lemma norm_im_le (a : Coeff p) : ‖imCLM p a‖ ≤ ‖a‖ := by
  apply lp.norm_mono (ne_of_gt (zero_lt_one.trans_le Fact.out))
  intro n
  exact Complex.abs_im_le_norm (a n)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The value of the complex extension. -/
def extensionValue (f : RealCoeff p →L[ℝ] F) (a : Coeff p) : F :=
  f (Coeff.reCLM p a)+Complex.I • f (imCLM p a)

/-- A uniform factor two bounds the complex extension. -/
lemma norm_extensionValue_le (f : RealCoeff p →L[ℝ] F) (a : Coeff p) :
    ‖extensionValue f a‖ ≤ (2*‖f‖)*‖a‖ := by
  calc
    ‖extensionValue f a‖ ≤ ‖f (Coeff.reCLM p a)‖+‖Complex.I • f (imCLM p a)‖ := norm_add_le _ _
    _ = ‖f (Coeff.reCLM p a)‖+‖f (imCLM p a)‖ := by rw [norm_smul,Complex.norm_I,one_mul]
    _ ≤ ‖f‖*‖Coeff.reCLM p a‖+‖f‖*‖imCLM p a‖ := add_le_add (f.le_opNorm _) (f.le_opNorm _)
    _ ≤ ‖f‖*‖a‖+‖f‖*‖a‖ := add_le_add (mul_le_mul_of_nonneg_left (norm_re_le a) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (norm_im_le a) (norm_nonneg _))
    _ = (2*‖f‖)*‖a‖ := by ring

lemma extensionValue_add (f : RealCoeff p →L[ℝ] F) (a b : Coeff p) :
    extensionValue f (a+b) = extensionValue f a+extensionValue f b := by
  simp only [extensionValue,map_add,smul_add]
  abel

lemma extensionValue_smul (f : RealCoeff p →L[ℝ] F) (z : ℂ) (a : Coeff p) :
    extensionValue f (z • a) = z • extensionValue f a := by
  simp only [extensionValue,re_smul,im_smul,map_sub,map_add,map_smul]
  simp only [← Complex.coe_smul,smul_add,smul_smul]
  have hz : z = (z.re : ℂ)+Complex.I*(z.im : ℂ) := by
    apply Complex.ext <;> simp
  conv_rhs => rw [hz]
  match_scalars <;> ring_nf
  simp [Complex.I_sq]

/-- The continuous complex-linear extension of a real coefficient map. -/
def complexifyLinear (f : RealCoeff p →L[ℝ] F) : Coeff p →L[ℂ] F :=
  LinearMap.mkContinuous
    { toFun := extensionValue f
      map_add' := extensionValue_add f
      map_smul' := extensionValue_smul f }
    (2*‖f‖) (norm_extensionValue_le f)

@[simp] lemma complexifyLinear_apply (f : RealCoeff p →L[ℝ] F) (a : Coeff p) :
    complexifyLinear f a = f (Coeff.reCLM p a)+Complex.I • f (imCLM p a) := rfl

/-- Operator norm control for complexification. -/
lemma norm_complexifyLinear_le (f : RealCoeff p →L[ℝ] F) : ‖complexifyLinear f‖ ≤ 2*‖f‖ :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- The extension agrees exactly on the included real sequence space. -/
@[simp] lemma complexifyLinear_real (f : RealCoeff p →L[ℝ] F) (a : RealCoeff p) :
    complexifyLinear f (RealCoeff.complexCLM p a) = f a := by
  have hi : imCLM p (RealCoeff.complexCLM p a) = 0 := by ext n; simp
  simp [hi]

/-- Complexification itself is a bounded linear operation on maps. -/
def complexifyCLM : (RealCoeff p →L[ℝ] F) →L[ℂ] (Coeff p →L[ℂ] F) :=
  LinearMap.mkContinuous
    { toFun := complexifyLinear
      map_add' := by intro f g; ext a; simp; abel
      map_smul' := by intro z f; ext a; simp [smul_add,smul_smul,mul_comm] }
    2 norm_complexifyLinear_le

lemma norm_complexifyCLM_le : ‖complexifyCLM (p := p) (F := F)‖ ≤ 2 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) _

end NLS.Coeff.Complexification
