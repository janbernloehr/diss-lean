import NLS.SequenceSpaces.NonnegativeRealAnalyticExtension
import NLS.ComplexAnalysis.LocalRealAxisDerivative
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! # Real matrix entries of derivatives from local real values -/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- Local reality on the full real locus makes each derivative matrix entry real. -/
theorem fderiv_entries_real_of_eventually_real
    {f : Coeff p → Coeff q} {c : Coeff p} (hc : c ∈ realLocus p)
    (hf : AnalyticAt ℂ f c)
    (hreal : ∀ᶠ y in 𝓝 c, y ∈ realLocus p → f y ∈ realLocus q)
    (m k : ℤ) : ((fderiv ℂ f c (lp.single p k 1)) m).im = 0 := by
  let v : Coeff p := lp.single p k 1
  let L := lp.evalCLM ℂ (fun _ : ℤ => ℂ) q m
  let P : ℂ → ℂ := fun z => L (f (c+z • v))
  have hline : HasDerivAt (fun z : ℂ => c+z • v) v 0 := by
    simpa only [one_smul,id_eq] using! ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add c
  have hfc : HasFDerivAt f (fderiv ℂ f c) (c+(0 : ℂ) • v) := by
    simpa only [zero_smul,add_zero] using hf.differentiableAt.hasFDerivAt
  have hd : HasDerivAt P (L (fderiv ℂ f c v)) 0 :=
    L.hasFDerivAt.comp_hasDerivAt 0 (hfc.comp_hasDerivAt 0 hline)
  apply ComplexAnalysis.HasDerivAt.im_eq_zero_of_eventually_real P _ 0 hd
  have ht : Tendsto (fun t : ℝ => c+(t : ℂ) • v) (𝓝 0) (𝓝 c) := by
    have hcont : Continuous (fun t : ℝ => c+(t : ℂ) • v) := by fun_prop
    simpa only [Complex.ofReal_zero,zero_smul,add_zero] using hcont.tendsto (0 : ℝ)
  filter_upwards [ht hreal] with t ht
  apply ht ?_ m
  intro n
  change (c n+(t : ℂ)*(lp.single p k 1 : Coeff p) n).im = 0
  by_cases hn : n = k <;> simp [lp.single_apply,hn,hc n,hc k]

end NLS.Coeff
