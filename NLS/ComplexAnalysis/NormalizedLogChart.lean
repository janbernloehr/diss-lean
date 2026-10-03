import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! # Local logarithms with a prescribed additive value

Normalizing the multiplier by its base value puts the logarithm near
one, independently of the multiplier's original argument. The base
value fixes the additive logarithm period.
-/
noncomputable section
open Set Filter Topology Complex
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def normalizedLogChart (M : E → ℂ) (a : E) (A : ℂ) (x : E) : ℂ :=
  A + log (M x/M a)

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
@[simp] theorem normalizedLogChart_base (M : E → ℂ) (a : E) (A : ℂ) (ha : M a ≠ 0) :
    normalizedLogChart M a A a = A := by simp [normalizedLogChart,ha]

theorem normalizedLogChart_analyticAt (M : E → ℂ) (a x : E) (A : ℂ)
    (hM : AnalyticAt ℂ M x) (hlog : M x/M a ∈ slitPlane) :
    AnalyticAt ℂ (normalizedLogChart M a A) x :=
  analyticAt_const.add ((hM.div_const).clog hlog)

theorem normalizedLogChart_hasFDerivAt (M : E → ℂ) (a x : E) (A : ℂ)
    (ha : M a ≠ 0) (hM : DifferentiableAt ℂ M x) (hlog : M x/M a ∈ slitPlane) :
    HasFDerivAt (normalizedLogChart M a A) ((M x)⁻¹ • fderiv ℂ M x) x := by
  have hd : HasFDerivAt (fun y => M y/M a) ((M a)⁻¹ • fderiv ℂ M x) x := by
    simpa only [smul_eq_mul,div_eq_inv_mul] using! hM.hasFDerivAt.const_smul (M a)⁻¹
  have h := (hd.clog hlog).const_add A
  convert! h using 1
  ext v
  simp only [smul_apply,smul_eq_mul,inv_div]
  field_simp

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
/-- Exponentiating the normalized chart recovers the multiplier,
with precisely the prescribed base factor. -/
theorem exp_normalizedLogChart (M : E → ℂ) (a x : E) (A : ℂ)
    (ha : M a ≠ 0) (hx : M x ≠ 0) :
    exp (normalizedLogChart M a A x) = exp A * M x / M a := by
  rw [normalizedLogChart,exp_add,exp_log (div_ne_zero hx ha),mul_div_assoc]

omit [NormedSpace ℂ E] in
/-- A continuous logarithm is recovered exactly near its base point;
the statement excludes an undetermined integer logarithm period. -/
theorem normalizedLogChart_eventually_eq (M F : E → ℂ) (a : E)
    (hF : ContinuousAt F a) (hexp : (fun x => exp (F x)) =ᶠ[𝓝 a] M) :
    normalizedLogChart M a (F a) =ᶠ[𝓝 a] F := by
  have hbase : exp (F a) = M a := hexp.eq_of_nhds
  have hi : Tendsto (fun x => (F x-F a).im) (𝓝 a) (𝓝 0) := by
    have hc : ContinuousAt (fun x => F x-F a) a := hF.sub continuousAt_const
    simpa only [sub_self,zero_im,Function.comp_def] using
      (Complex.continuous_im.tendsto (F a-F a)).comp hc.tendsto
  filter_upwards [hexp,hi.eventually (Ioo_mem_nhds (neg_neg_of_pos Real.pi_pos) Real.pi_pos)] with x hx him
  rw [normalizedLogChart,← hbase,← hx,← exp_sub,log_exp him.1 him.2.le]
  exact add_sub_cancel _ _

end NLS.ComplexAnalysis
