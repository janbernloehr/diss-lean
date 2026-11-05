import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Module

/-! A real form with contractive real and imaginary projections admits
bounded complexification of linear maps, with the exact factor two bound. -/
noncomputable section
open Complex
namespace NLS.ComplexAnalysis
variable (R E : Type*) [NormedAddCommGroup R] [NormedSpace ℝ R]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

structure ContractiveComplexification where
  inclusion : R →L[ℝ] E
  re : E →L[ℝ] R
  im : E →L[ℝ] R
  re_inclusion : ∀ x, re (inclusion x)=x
  im_inclusion : ∀ x, im (inclusion x)=0
  re_I : ∀ z, re (I • z)= -im z
  im_I : ∀ z, im (I • z)=re z
  norm_re : ∀ z, ‖re z‖≤‖z‖
  norm_im : ∀ z, ‖im z‖≤‖z‖
  decomposition : ∀ z, inclusion (re z)+I • inclusion (im z)=z

namespace ContractiveComplexification
variable {R E}

theorem re_smul (c : ContractiveComplexification R E) (z : ℂ) (a : E) :
    c.re (z • a)=z.re • c.re a-z.im • c.im a := by
  have hz : z=(z.re:ℂ)+I*(z.im:ℂ) := by apply Complex.ext <;> simp
  conv_lhs => rw [hz]
  simp only [add_smul,mul_smul,Complex.coe_smul,map_add,map_smul,c.re_I]
  abel

theorem im_smul (c : ContractiveComplexification R E) (z : ℂ) (a : E) :
    c.im (z • a)=z.re • c.im a+z.im • c.re a := by
  have hz : z=(z.re:ℂ)+I*(z.im:ℂ) := by apply Complex.ext <;> simp
  conv_lhs => rw [hz]
  simp only [add_smul,mul_smul,Complex.coe_smul,map_add,map_smul,c.im_I]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

def extensionValue (c : ContractiveComplexification R E) (f : R →L[ℝ] F) (a : E) : F :=
  f (c.re a)+I • f (c.im a)

theorem norm_extensionValue_le (c : ContractiveComplexification R E) (f : R →L[ℝ] F) (a : E) :
    ‖c.extensionValue f a‖≤(2*‖f‖)*‖a‖ := by
  calc
    ‖c.extensionValue f a‖ ≤ ‖f (c.re a)‖+‖I • f (c.im a)‖ := norm_add_le _ _
    _ = ‖f (c.re a)‖+‖f (c.im a)‖ := by rw [norm_smul,Complex.norm_I,one_mul]
    _ ≤ ‖f‖*‖c.re a‖+‖f‖*‖c.im a‖ := add_le_add (f.le_opNorm _) (f.le_opNorm _)
    _ ≤ ‖f‖*‖a‖+‖f‖*‖a‖ := add_le_add
      (mul_le_mul_of_nonneg_left (c.norm_re a) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (c.norm_im a) (norm_nonneg _))
    _ = (2*‖f‖)*‖a‖ := by ring

theorem extensionValue_add (c : ContractiveComplexification R E) (f : R →L[ℝ] F) (a b : E) :
    c.extensionValue f (a+b)=c.extensionValue f a+c.extensionValue f b := by
  simp only [extensionValue,map_add,smul_add]
  abel

theorem extensionValue_smul (c : ContractiveComplexification R E) (f : R →L[ℝ] F) (z : ℂ) (a : E) :
    c.extensionValue f (z • a)=z • c.extensionValue f a := by
  simp only [extensionValue,c.re_smul,c.im_smul,map_sub,map_add,map_smul]
  simp only [← Complex.coe_smul,smul_add,smul_smul]
  have hz : z=(z.re:ℂ)+I*(z.im:ℂ) := by apply Complex.ext <;> simp
  conv_rhs => rw [hz]
  match_scalars <;> ring_nf
  simp [Complex.I_sq]

def complexifyLinear (c : ContractiveComplexification R E) (f : R →L[ℝ] F) : E →L[ℂ] F :=
  LinearMap.mkContinuous
    { toFun := c.extensionValue f
      map_add' := c.extensionValue_add f
      map_smul' := c.extensionValue_smul f }
    (2*‖f‖) (c.norm_extensionValue_le f)

theorem complexifyLinear_apply (c : ContractiveComplexification R E) (f : R →L[ℝ] F) (a : E) :
    c.complexifyLinear f a=f (c.re a)+I • f (c.im a) := rfl

theorem norm_complexifyLinear_le (c : ContractiveComplexification R E) (f : R →L[ℝ] F) :
    ‖c.complexifyLinear f‖≤2*‖f‖ := LinearMap.mkContinuous_norm_le _ (by positivity) _

theorem complexifyLinear_real (c : ContractiveComplexification R E) (f : R →L[ℝ] F) (a : R) :
    c.complexifyLinear f (c.inclusion a)=f a := by
  simp only [complexifyLinear_apply,c.re_inclusion,c.im_inclusion,map_zero,smul_zero,add_zero]

def complexifyCLM (c : ContractiveComplexification R E) :
    (R →L[ℝ] F) →L[ℂ] (E →L[ℂ] F) :=
  LinearMap.mkContinuous
    { toFun := c.complexifyLinear
      map_add' := by
        intro f g
        ext a
        change (f (c.re a)+g (c.re a))+I • (f (c.im a)+g (c.im a))=
          (f (c.re a)+I • f (c.im a))+(g (c.re a)+I • g (c.im a))
        rw [smul_add]
        abel
      map_smul' := by
        intro z f
        ext a
        change z • f (c.re a)+I • (z • f (c.im a))=z • (f (c.re a)+I • f (c.im a))
        rw [smul_add,smul_smul,smul_smul,mul_comm I z] }
    2 (c.norm_complexifyLinear_le)

theorem norm_complexifyCLM_le (c : ContractiveComplexification R E) :
    ‖c.complexifyCLM (F := F)‖≤2 := LinearMap.mkContinuous_norm_le _ (by norm_num) _

end ContractiveComplexification
end NLS.ComplexAnalysis
