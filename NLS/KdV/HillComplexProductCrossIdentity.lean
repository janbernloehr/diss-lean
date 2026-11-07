import NLS.KdV.HillCanonicalZeroProducts
import NLS.KdV.HillEnergyProductComplexZeros

/-! Real-form analytic identity fixes the complex numerator/product
ratio simultaneously at EVERY pair of energies on the WHOLE connected
common source domain. No analytic scalar or universal value is assumed. -/
noncomputable section
open Set Metric Complex
open scoped ENNReal Classical
namespace NLS.KdV

theorem hillHminusCanonicalPsi_product_cross_identity (n : ℕ+) (E F : ℂ)
    (q : PeriodOneHminusOne) (hq : q ∈ hillHminusCanonicalZeroSequenceDomain) :
    hillHminusCanonicalPsi n (E,q)*hillHminusCanonicalZeroProduct n (F,q) =
      hillHminusCanonicalPsi n (F,q)*hillHminusCanonicalZeroProduct n (E,q) := by
  let U := hillHminusCanonicalZeroSequenceDomain
  have hsub := hillHminusCanonicalZeroSequenceDomain_subset_psiDomain
  have hψ (E : ℂ) : AnalyticOnNhd ℂ (fun a => hillHminusCanonicalPsi n (E,a)) U := by
    intro a ha
    exact (analyticOnNhd_hillHminusCanonicalPsi n (E,a) ⟨mem_univ _,hsub ha⟩).comp
      (f := fun b : PeriodOneHminusOne => (E,b)) (analyticAt_const.prod analyticAt_id)
  have hP (E : ℂ) : AnalyticOnNhd ℂ (fun a => hillHminusCanonicalZeroProduct n (E,a)) U := by
    intro a ha
    exact (analyticOnNhd_hillHminusCanonicalZeroProduct n (E,a) ⟨mem_univ _,ha⟩).comp
      (f := fun b : PeriodOneHminusOne => (E,b)) (analyticAt_const.prod analyticAt_id)
  have hzero : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have he := analytic_eqOn_of_real_periodOneHminus U isOpen_hillHminusCanonicalZeroSequenceDomain
    isConnected_hillHminusCanonicalZeroSequenceDomain.isPreconnected
    ⟨0,real_mem_hillHminusCanonicalZeroSequenceDomain 0 hzero,hzero⟩
    (fun a => hillHminusCanonicalPsi n (E,a)*hillHminusCanonicalZeroProduct n (F,a))
    (fun a => hillHminusCanonicalPsi n (F,a)*hillHminusCanonicalZeroProduct n (E,a))
    ((hψ E).mul (hP F)) ((hψ F).mul (hP E)) (by
      intro a _ har
      rw [hillHminusCanonicalZeroProduct_real n F ⟨a,har⟩,hillHminusCanonicalZeroProduct_real n E ⟨a,har⟩,
        hillHminusCanonicalPsi_eq_scalar_mul_literalProduct n E ⟨a,har⟩,
        hillHminusCanonicalPsi_eq_scalar_mul_literalProduct n F ⟨a,har⟩]
      ring)
  exact he hq

theorem exists_unique_hillHminusCanonicalPsi_complex_product_scalar (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ hillHminusCanonicalZeroSequenceDomain) :
    ∃! A : ℂ, ∀ E : ℂ, hillHminusCanonicalPsi n (E,q) = A*hillHminusCanonicalZeroProduct n (E,q) := by
  obtain ⟨F,hF⟩ := exists_hillEnergySequenceProduct_ne_zero n (hillHminusCanonicalZeroSequence n q)
  change hillHminusCanonicalZeroProduct n (F,q) ≠ 0 at hF
  let A := hillHminusCanonicalPsi n (F,q)/hillHminusCanonicalZeroProduct n (F,q)
  have hA (E : ℂ) : hillHminusCanonicalPsi n (E,q) = A*hillHminusCanonicalZeroProduct n (E,q) := by
    dsimp only [A]
    rw [div_mul_eq_mul_div]
    exact (eq_div_iff hF).mpr (hillHminusCanonicalPsi_product_cross_identity n E F q hq)
  refine ⟨A,hA,?_⟩
  intro B hB
  exact mul_right_cancel₀ hF ((hB F).symm.trans (hA F))

end NLS.KdV
