import NLS.KdV.HillComplexProductCrossIdentity

/-! The ACTUAL canonical Hill numerator has a unique NONZERO analytic
product scalar on the WHOLE common complex zero-sequence domain. Its
universal value is not inferred from real identity or the free value. -/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal Classical
namespace NLS.KdV

def hillHminusCanonicalPsiProductScalar (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  if hq : q ∈ hillHminusCanonicalZeroSequenceDomain then
    Classical.choose (exists_unique_hillHminusCanonicalPsi_complex_product_scalar n q hq).exists
  else 0

theorem hillHminusCanonicalPsi_eq_complex_scalar_mul_product (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusCanonicalZeroSequenceDomain) (E : ℂ) :
    hillHminusCanonicalPsi n (E,q) = hillHminusCanonicalPsiProductScalar n q*hillHminusCanonicalZeroProduct n (E,q) := by
  rw [hillHminusCanonicalPsiProductScalar,dif_pos hq]
  exact Classical.choose_spec (exists_unique_hillHminusCanonicalPsi_complex_product_scalar n q hq).exists E

theorem hillHminusCanonicalPsiProductScalar_ne_zero (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusCanonicalZeroSequenceDomain) : hillHminusCanonicalPsiProductScalar n q ≠ 0 := by
  intro hz
  apply hillHminusCanonicalPsi_energy_ne_zero n q (hillHminusCanonicalZeroSequenceDomain_subset_psiDomain hq)
  funext E
  rw [hillHminusCanonicalPsi_eq_complex_scalar_mul_product n q hq E,hz,zero_mul]
  rfl

theorem hillHminusCanonicalPsiProductScalar_unique (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusCanonicalZeroSequenceDomain) (A : ℂ)
    (hA : ∀ E : ℂ, hillHminusCanonicalPsi n (E,q) = A*hillHminusCanonicalZeroProduct n (E,q)) :
    A = hillHminusCanonicalPsiProductScalar n q := by
  obtain ⟨E,hE⟩ := exists_hillEnergySequenceProduct_ne_zero n (hillHminusCanonicalZeroSequence n q)
  exact mul_right_cancel₀ hE ((hA E).symm.trans (hillHminusCanonicalPsi_eq_complex_scalar_mul_product n q hq E))

theorem hillHminusCanonicalPsiProductScalar_eq_ratio (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusCanonicalZeroSequenceDomain) (E : ℂ)
    (hE : hillHminusCanonicalZeroProduct n (E,q) ≠ 0) :
    hillHminusCanonicalPsiProductScalar n q = hillHminusCanonicalPsi n (E,q)/hillHminusCanonicalZeroProduct n (E,q) :=
  (eq_div_iff hE).mpr (hillHminusCanonicalPsi_eq_complex_scalar_mul_product n q hq E).symm

theorem analyticOnNhd_hillHminusCanonicalPsiProductScalar (n : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusCanonicalPsiProductScalar n) hillHminusCanonicalZeroSequenceDomain := by
  intro q hq
  obtain ⟨E,hE⟩ := exists_hillEnergySequenceProduct_ne_zero n (hillHminusCanonicalZeroSequence n q)
  change hillHminusCanonicalZeroProduct n (E,q) ≠ 0 at hE
  have hψ := (analyticOnNhd_hillHminusCanonicalPsi n (E,q)
    ⟨mem_univ _,hillHminusCanonicalZeroSequenceDomain_subset_psiDomain hq⟩).comp
    (f := fun a : PeriodOneHminusOne => (E,a)) (analyticAt_const.prod analyticAt_id)
  have hP := (analyticOnNhd_hillHminusCanonicalZeroProduct n (E,q) ⟨mem_univ _,hq⟩).comp
    (f := fun a : PeriodOneHminusOne => (E,a)) (analyticAt_const.prod analyticAt_id)
  apply (hψ.div hP hE).congr
  filter_upwards [isOpen_hillHminusCanonicalZeroSequenceDomain.mem_nhds hq,hP.continuousAt.eventually_ne hE] with a ha hPa
  exact (hillHminusCanonicalPsiProductScalar_eq_ratio n a ha E hPa).symm

theorem hillHminusCanonicalPsiProductScalar_real (n : ℕ+) (q : PeriodOneRealHminusOne) :
    hillHminusCanonicalPsiProductScalar n q.val = hillHminusPsiProductScalar n q.val q.property := by
  apply (hillHminusCanonicalPsiProductScalar_unique n q.val
    (real_mem_hillHminusCanonicalZeroSequenceDomain q.val q.property) _ ?_).symm
  intro E
  rw [hillHminusCanonicalZeroProduct_real]
  exact hillHminusCanonicalPsi_eq_scalar_mul_literalProduct n E q

theorem hillHminusCanonicalPsi_complex_zero_iff (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusCanonicalZeroSequenceDomain) (E : ℂ) :
    hillHminusCanonicalPsi n (E,q) = 0 ↔ ∃ m : ℕ+, m ≠ n ∧
      E = hillEnergySequenceZero m (hillHminusCanonicalZeroSequence n q) := by
  rw [hillHminusCanonicalPsi_eq_complex_scalar_mul_product n q hq E,mul_eq_zero]
  simp only [hillHminusCanonicalPsiProductScalar_ne_zero n q hq,false_or]
  exact hillEnergySequenceProduct_eq_zero_iff n E _

end NLS.KdV
