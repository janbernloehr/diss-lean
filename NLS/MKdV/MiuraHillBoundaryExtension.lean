import NLS.MKdV.SobolevMiuraPrimitive
import NLS.ComplexAnalysis.NonrealBoundaryExtension
import NLS.ComplexAnalysis.EntireEvenSquareDescent

/-! # Filling the independent Miura Hill sheets across real bands

The values are limits of the independently constructed quasi-Hill root
and primitive from nonreal energies. The NLS comparison proves existence
and analyticity of these limits, rather than defining the limits by NLS.
-/
noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis NLS.KdV NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def canonicalMiuraHillRoot (a : ScalarDomain 2) : ℂ → ℂ :=
  nonrealBoundaryExtension (fun μ => miuraHillRoot (μ,periodOneMiuraCurve a))

def canonicalMiuraHillPrimitive (a : ScalarDomain 2) : ℂ → ℂ :=
  nonrealBoundaryExtension (fun μ => miuraHillPrimitive (μ,periodOneMiuraCurve a))

theorem sqrt_sq_of_re_pos (z : ℂ) (hz : 0 < z.re) : Complex.sqrt (z^2) = z := by
  have h := classicalHillFreePrimitive_sq_of_re_pos z hz
  exact mul_left_cancel₀ (neg_ne_zero.mpr I_ne_zero) h

theorem sq_mem_slitPlane_of_re_pos (z : ℂ) (hz : 0 < z.re) : z^2 ∈ slitPlane := by
  apply mem_slitPlane_iff.mpr
  by_cases hi : z.im = 0
  · left
    simp only [pow_two,mul_re,hi,mul_zero,sub_zero]
    exact mul_pos hz hz
  · right
    simp only [pow_two,mul_im]
    intro he
    apply mul_ne_zero hz.ne' hi
    nlinarith

theorem sqrt_re_pos_of_im_ne_zero (μ : ℂ) (hi : μ.im ≠ 0) :
    0 < (Complex.sqrt μ).re ∧ (Complex.sqrt μ).im ≠ 0 := by
  have hs := complex_sqrt_sq μ
  have hnonneg : 0 ≤ (Complex.sqrt μ).re := by
    rw [Complex.sqrt,cpow_inv_two_re]
    positivity
  have him := congrArg Complex.im hs
  simp only [pow_two,mul_im] at him
  constructor
  · by_contra hn
    have he : (Complex.sqrt μ).re = 0 := le_antisymm (le_of_not_gt hn) hnonneg
    rw [he,zero_mul,mul_zero,zero_add] at him
    exact hi him.symm
  · intro he
    rw [he,zero_mul,mul_zero,zero_add] at him
    exact hi him.symm

theorem miuraHillSheets_nonreal_eq_sqrt_NLS (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (μ : ℂ) (hi : μ.im ≠ 0) :
    miuraHillRoot (μ,periodOneMiuraCurve a) =
      sourceCanonicalRoot (by simp) (by norm_num) (realDiagonalH1Source a ha).val (Complex.sqrt μ) ∧
    miuraHillPrimitive (μ,periodOneMiuraCurve a) =
      sourceAbelianPrimitive (by simp) (by norm_num) (realDiagonalH1Source a ha).val
        (realDiagonalH1Source a ha).property (Complex.sqrt μ) := by
  have h := periodOneMiura_sheets_eq_NLS a ha (Complex.sqrt μ)
    (sqrt_re_pos_of_im_ne_zero μ hi).1 (sqrt_re_pos_of_im_ne_zero μ hi).2
  simpa only [complex_sqrt_sq] using h

theorem canonicalMiuraHillSheets_eq_NLS (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (z : ℂ) (hzr : 0 < z.re)
    (hz : z ∈ sourceCanonicalRootDomain (by simp) (by norm_num) (realDiagonalH1Source a ha).val) :
    canonicalMiuraHillRoot a (z^2) =
      sourceCanonicalRoot (by simp) (by norm_num) (realDiagonalH1Source a ha).val z ∧
    canonicalMiuraHillPrimitive a (z^2) =
      sourceAbelianPrimitive (by simp) (by norm_num) (realDiagonalH1Source a ha).val
        (realDiagonalH1Source a ha).property z := by
  have hs : AnalyticAt ℂ Complex.sqrt (z^2) := Complex.differentiableOn_sqrt.analyticAt
    (isOpen_slitPlane.mem_nhds (sq_mem_slitPlane_of_re_pos z hzr))
  have hR : AnalyticAt ℂ (fun μ => sourceCanonicalRoot (by simp) (by norm_num)
      (realDiagonalH1Source a ha).val (Complex.sqrt μ)) (z^2) := by
    have hr : AnalyticAt ℂ (sourceCanonicalRoot (by simp) (by norm_num)
        (realDiagonalH1Source a ha).val) (Complex.sqrt (z^2)) := by
      rw [sqrt_sq_of_re_pos z hzr]
      exact sourceCanonicalRoot_analyticOnNhd _ _ _ z hz
    exact hr.comp hs
  have hF : AnalyticAt ℂ (fun μ => sourceAbelianPrimitive (by simp) (by norm_num)
      (realDiagonalH1Source a ha).val (realDiagonalH1Source a ha).property (Complex.sqrt μ)) (z^2) := by
    have hf : AnalyticAt ℂ (sourceAbelianPrimitive (by simp) (by norm_num)
        (realDiagonalH1Source a ha).val (realDiagonalH1Source a ha).property) (Complex.sqrt (z^2)) := by
      rw [sqrt_sq_of_re_pos z hzr]
      exact sourceAbelianPrimitive_analyticAt_of_mem_rootDomain _ _ _ _ z hz
    exact hf.comp hs
  constructor
  · have he := nonrealBoundaryExtension_eq_of_continuousAt hR.continuousAt
      (fun μ hi => (miuraHillSheets_nonreal_eq_sqrt_NLS a ha μ hi).1)
    simpa only [canonicalMiuraHillRoot,sqrt_sq_of_re_pos z hzr] using he
  · have he := nonrealBoundaryExtension_eq_of_continuousAt hF.continuousAt
      (fun μ hi => (miuraHillSheets_nonreal_eq_sqrt_NLS a ha μ hi).2)
    simpa only [canonicalMiuraHillPrimitive,sqrt_sq_of_re_pos z hzr] using he

theorem analyticAt_canonicalMiuraHillSheets (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (μ : ℂ) (hμ : μ ∈ slitPlane)
    (hz : Complex.sqrt μ ∈ sourceCanonicalRootDomain (by simp) (by norm_num)
      (realDiagonalH1Source a ha).val) :
    AnalyticAt ℂ (canonicalMiuraHillRoot a) μ ∧ AnalyticAt ℂ (canonicalMiuraHillPrimitive a) μ := by
  have hs : AnalyticAt ℂ Complex.sqrt μ := Complex.differentiableOn_sqrt.analyticAt
    (isOpen_slitPlane.mem_nhds hμ)
  exact ⟨analyticAt_nonrealBoundaryExtension ((sourceCanonicalRoot_analyticOnNhd _ _ _ _ hz).comp hs)
      (fun w hi => (miuraHillSheets_nonreal_eq_sqrt_NLS a ha w hi).1),
    analyticAt_nonrealBoundaryExtension ((sourceAbelianPrimitive_analyticAt_of_mem_rootDomain _ _ _ _ _ hz).comp hs)
      (fun w hi => (miuraHillSheets_nonreal_eq_sqrt_NLS a ha w hi).2)⟩

theorem canonicalMiuraHillRoot_eq_original (a : ScalarDomain 2) (μ : ℂ)
    (ht : (μ,periodOneMiuraCurve a) ∈ miuraHillContinuationDomain) :
    canonicalMiuraHillRoot a μ = miuraHillRoot (μ,periodOneMiuraCurve a) := by
  apply nonrealBoundaryExtension_eq_self
  exact ((quasiHillPrimitiveData.root_analytic _ ht).comp
    (f := fun w : ℂ => (w,periodOneMiuraCurve a)) (analyticAt_id.prod analyticAt_const)).continuousAt

theorem canonicalMiuraHillPrimitive_eq_original (a : ScalarDomain 2) (μ : ℂ)
    (ht : (μ,periodOneMiuraCurve a) ∈ miuraHillContinuationDomain) :
    canonicalMiuraHillPrimitive a μ = miuraHillPrimitive (μ,periodOneMiuraCurve a) := by
  apply nonrealBoundaryExtension_eq_self
  exact ((quasiHillPrimitiveData.primitive_analytic _ ht).comp
    (f := fun w : ℂ => (w,periodOneMiuraCurve a)) (analyticAt_id.prod analyticAt_const)).continuousAt

end NLS.MKdV
