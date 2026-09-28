import NLS.ComplexAnalysis.EqualOrderQuotient

/-!
# Filling a quotient at simple denominator zeros

For interpolation uniqueness, the numerator may have additional zeros.
It is enough that it vanishes at every simple zero of the denominator:
the quotient has no poles, though it may itself vanish.
-/

noncomputable section
open Set
namespace NLS.ComplexAnalysis

theorem analyticOnNhd_analyticQuotient_of_simple_zeros
    {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ)
    (hg : AnalyticOnNhd ℂ g Set.univ)
    (hcommon : ∀ z, g z = 0 → f z = 0)
    (hsimple : ∀ z, g z = 0 → deriv g z ≠ 0) :
    AnalyticOnNhd ℂ (analyticQuotient f g) Set.univ := by
  intro z _
  have hfz : AnalyticAt ℂ f z := hf z (mem_univ _)
  have hgz : AnalyticAt ℂ g z := hg z (mem_univ _)
  apply (meromorphicNFOn_toMeromorphicNFOn (f/g) Set.univ (mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
  rw [meromorphicOrderAt_toMeromorphicNFOn (hf.meromorphicOn.div hg.meromorphicOn) (mem_univ z),
    meromorphicOrderAt_div hfz.meromorphicAt hgz.meromorphicAt,
    hfz.meromorphicOrderAt_eq,hgz.meromorphicOrderAt_eq]
  by_cases hzero : g z = 0
  · have ho : analyticOrderAt g z = 1 :=
      hgz.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hzero (hsimple z hzero)
    have horder : 1 ≤ analyticOrderAt f z := by
      have hne : analyticOrderAt f z ≠ 0 :=
        hfz.analyticOrderAt_ne_zero.mpr (hcommon z hzero)
      exact Order.one_le_iff_ne_zero.mpr hne
    rw [ho]
    by_cases htop : analyticOrderAt f z = ⊤
    · simp [htop]
    · lift analyticOrderAt f z to ℕ using htop with k hk
      have hkpos : 1 ≤ k := by exact_mod_cast horder
      change (0 : WithTop ℤ) ≤ (k : WithTop ℤ) - (1 : WithTop ℤ)
      have hcast : (1 : WithTop ℤ) = ((1:ℤ) : WithTop ℤ) := by norm_num
      rw [hcast]
      exact_mod_cast (show (0:ℤ) ≤ (k:ℤ)-1 by omega)
  · have ho : analyticOrderAt g z = 0 :=
      hgz.analyticOrderAt_eq_zero.mpr hzero
    simp [ho]

theorem analyticQuotient_mul_of_simple_zeros
    {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ)
    (hg : AnalyticOnNhd ℂ g Set.univ)
    (hcommon : ∀ z, g z = 0 → f z = 0)
    (z : ℂ) :
    analyticQuotient f g z * g z = f z := by
  by_cases hzero : g z = 0
  · simp [hzero,hcommon z hzero]
  · rw [analyticQuotient_eq_div hf hg z hzero,div_mul_cancel₀ _ hzero]

end NLS.ComplexAnalysis
