import NLS.SequenceSpaces.RealCoeffNorm
import NLS.ComplexAnalysis.ContractiveAnalyticExtension

/-! Contractive complexification of real coefficient pairs, with their
actual product norms and coefficientwise real inclusion. -/
noncomputable section
open Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.Coeff
variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

def imCLM : Coeff p →L[ℝ] RealCoeff p :=
  lp.mapCLM p (fun _ => Complex.imCLM) (norm_nonneg _) (fun _ => le_rfl)

theorem norm_reCLM_le (z : Coeff p) : ‖reCLM p z‖ ≤ ‖z‖ := by
  apply lp.norm_mono (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p)))
  intro k
  exact Complex.abs_re_le_norm (z k)

theorem norm_imCLM_le (z : Coeff p) : ‖imCLM p z‖ ≤ ‖z‖ := by
  apply lp.norm_mono (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p)))
  intro k
  exact Complex.abs_im_le_norm (z k)

def realPairContractiveComplexification :
    ContractiveComplexification (RealCoeff p × RealCoeff p) (Coeff p × Coeff p) where
  inclusion := (RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)
  re := (reCLM p).prodMap (reCLM p)
  im := (imCLM p).prodMap (imCLM p)
  re_inclusion x := by ext k <;> rfl
  im_inclusion x := by ext k <;> rfl
  re_I z := by
    apply Prod.ext
    · ext k
      change (I * z.1 k).re = -(z.1 k).im
      simp
    · ext k
      change (I * z.2 k).re = -(z.2 k).im
      simp
  im_I z := by
    apply Prod.ext
    · ext k
      change (I * z.1 k).im = (z.1 k).re
      simp
    · ext k
      change (I * z.2 k).im = (z.2 k).re
      simp
  norm_re z := by
    exact max_le_max (norm_reCLM_le p z.1) (norm_reCLM_le p z.2)
  norm_im z := by
    exact max_le_max (norm_imCLM_le p z.1) (norm_imCLM_le p z.2)
  decomposition z := by
    apply Prod.ext
    · ext k
      change ((z.1 k).re:ℂ)+I*((z.1 k).im:ℂ)=z.1 k
      simpa only [mul_comm] using Complex.re_add_im (z.1 k)
    · ext k
      change ((z.2 k).re:ℂ)+I*((z.2 k).im:ℂ)=z.2 k
      simpa only [mul_comm] using Complex.re_add_im (z.2 k)

end NLS.Coeff
