import NLS.ZakharovShabat.SingleSpectralProductOrders
import NLS.ComplexAnalysis.IsolatedOrderStability

/-!
# Exact analytic orders of the critical product

An isolating disc and Rouché stability pass the finite cutoff multiplicities
to the entire limit. These are the derivative's actual analytic orders.
-/

noncomputable section
open Filter Topology Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every parameter has a closed disc containing no other critical point. -/
theorem exists_criticalPoint_isolating_closedBall (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) (z : ℂ) :
    ∃ r : ℝ, 0 < r ∧ ∀ a ∈ closedBall z r, deriv (canonicalDiscriminant hp φ) a = 0 → a = z := by
  have he := eventually_discriminant_derivative_ne_zero hp hp1 φ hφ z
  rw [eventually_nhdsWithin_iff] at he
  obtain ⟨r,hr,hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp he
  refine ⟨r,hr,fun a ha hzero => ?_⟩
  by_contra hne
  exact hball ha hne hzero

variable {hp : p ≠ ⊤} {hp1 : 1 < p} {φ : PairSpace p} {hφ : φ ∈ pairParitySubspace 0}
variable {N : ℕ} {ξ : ℤ → ℂ}

/-- The critical product's natural analytic orders are exactly those of the derivative. -/
theorem CriticalPointLabeling.product_analyticOrderNatAt (h : CriticalPointLabeling hp hp1 φ hφ N ξ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p) (z : ℂ) :
    analyticOrderNatAt (entireSingleSpectralProduct ξ) z =
      analyticOrderNatAt (deriv (canonicalDiscriminant hp φ)) z := by
  obtain ⟨r,hr,hiso⟩ := exists_criticalPoint_isolating_closedBall hp hp1 φ hφ z
  have hFz (M : ℕ) (a : ℂ) (ha : a ∈ closedBall z r)
      (ha0 : singleSpectralPartialProduct ξ a M = 0) : a = z := by
    apply hiso a ha
    by_contra hnot
    exact singleSpectralPartialProduct_ne_zero ξ a
      (fun n hn => hnot (hn ▸ h.is_critical n)) M ha0
  have hgz (a : ℂ) (ha : a ∈ closedBall z r)
      (ha0 : entireSingleSpectralProduct ξ a = 0) : a = z :=
    hiso a ha ((h.product_eq_zero_iff hp hp1 φ hφ N ξ hξ a).mp ha0)
  have hconv := tendstoLocallyUniformlyOn_entireSingleSpectralProduct hp ξ hξ
  have hstab := NLS.ComplexAnalysis.eventually_analyticOrderNatAt_eq_of_isolated _ _ z r hr
    (fun M => (analyticOnNhd_singleSpectralPartialProduct ξ M).mono (Set.subset_univ _))
    ((analyticOnNhd_entireSingleSpectralProduct hp ξ hξ).mono (Set.subset_univ _)) hFz hgz
    ((tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_sphere z r)).mp
      (hconv.mono (Set.subset_univ _)))
  obtain ⟨M,hM,hpoly⟩ := (hstab.and (h.eventually_cutoff_order z)).exists
  have hn := congrArg ENat.toNat hpoly
  have hn' : analyticOrderNatAt (fun t => singleSpectralPartialProduct ξ t M) z =
      analyticOrderNatAt (deriv (canonicalDiscriminant hp φ)) z := by
    simpa only [analyticOrderNatAt, ENat.toNat_natCast] using hn
  exact hM.symm.trans hn'

/-- The entire critical product has finite order everywhere. -/
theorem CriticalPointLabeling.product_analyticOrderAt_ne_top (h : CriticalPointLabeling hp hp1 φ hφ N ξ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p) (z : ℂ) :
    analyticOrderAt (entireSingleSpectralProduct ξ) z ≠ ⊤ := by
  obtain ⟨r,hr,hiso⟩ := exists_criticalPoint_isolating_closedBall hp hp1 φ hφ z
  exact NLS.ComplexAnalysis.analyticOrderAt_ne_top_of_isolated _ z r hr
    ((analyticOnNhd_entireSingleSpectralProduct hp ξ hξ).mono (Set.subset_univ _))
    (fun a ha ha0 => hiso a ha ((h.product_eq_zero_iff hp hp1 φ hφ N ξ hξ a).mp ha0))

/-- Full extended orders agree, retaining finiteness as well as the multiplicity of each root. -/
theorem CriticalPointLabeling.product_analyticOrderAt (h : CriticalPointLabeling hp hp1 φ hφ N ξ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p) (z : ℂ) :
    analyticOrderAt (entireSingleSpectralProduct ξ) z =
      analyticOrderAt (deriv (canonicalDiscriminant hp φ)) z := by
  rw [← Nat.cast_analyticOrderNatAt (h.product_analyticOrderAt_ne_top hξ z),
    ← Nat.cast_analyticOrderNatAt (analyticOrderAt_discriminant_derivative_ne_top hp hp1 φ hφ z),
    h.product_analyticOrderNatAt hξ z]

end NLS.ZakharovShabat
