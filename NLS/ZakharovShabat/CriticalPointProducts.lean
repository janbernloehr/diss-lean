import NLS.ZakharovShabat.SingleSpectralProductsExterior
import NLS.ZakharovShabat.UniformCriticalDisplacements
import NLS.ComplexAnalysis.LimitNonvanishing

/-!
# Entire products over actual critical points

Reciprocal maximum-modulus bounds show that extension through the free lattice
adds no zeros. A complete critical-point sequence therefore gives an entire
product whose zero set is exactly that of the discriminant derivative.
Equality of analytic orders and identification of the two functions are separate.
-/

noncomputable section
open Filter Topology Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- No finite cutoff vanishes away from the chosen root sequence. -/
theorem singleSpectralPartialProduct_ne_zero (ξ : ℤ → ℂ) (z : ℂ)
    (hz : ∀ n, ξ n ≠ z) (N : ℕ) : singleSpectralPartialProduct ξ z N ≠ 0 := by
  unfold singleSpectralPartialProduct
  apply mul_ne_zero (by norm_num)
  exact Finset.prod_ne_zero_iff.mpr (fun n _ =>
    div_ne_zero (sub_ne_zero.mpr (hz n)) (singleSpectralDenominator_ne_zero n))

/-- For a closed root set, filling the free lattice introduces no additional zeros. -/
theorem entireSingleSpectralProduct_eq_zero_iff (hp : p ≠ ⊤) (ξ : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p) (hclosed : IsClosed (Set.range ξ))
    (z : ℂ) : entireSingleSpectralProduct ξ z = 0 ↔ ∃ n, ξ n = z := by
  constructor
  · intro he
    by_contra hz
    have hz' : z ∈ (Set.range ξ)ᶜ := hz
    obtain ⟨R,hR,hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
      (hclosed.isOpen_compl.mem_nhds hz')
    obtain ⟨r,hr0,hrR,hs⟩ := NLS.ComplexAnalysis.exists_small_sphere_subset_compl_countable
      freeLattice countable_freeLattice z R hR
    have hout (a : ℂ) (ha : a ∈ closedBall z r) : a ∉ Set.range ξ :=
      hball (closedBall_subset_closedBall hrR.le ha)
    have hconv := tendstoLocallyUniformlyOn_entireSingleSpectralProduct hp ξ hξ
    have han := analyticOnNhd_entireSingleSpectralProduct hp ξ hξ
    have hn : entireSingleSpectralProduct ξ z ≠ 0 := by
      apply NLS.ComplexAnalysis.limit_ne_zero_of_nonzero_on_closedBall _ _ z r hr0
        (fun N => differentiableOn_univ.mp (analyticOnNhd_singleSpectralPartialProduct ξ N).differentiableOn)
        (fun N a ha => singleSpectralPartialProduct_ne_zero ξ a
          (fun n hn => hout a ha ⟨n, hn⟩) N)
        (han.continuousOn.mono (Set.subset_univ _))
      · intro a ha hzero
        exact hout a (sphere_subset_closedBall ha)
          ((entireSingleSpectralProduct_eq_zero_iff_offLattice hp ξ hξ a (hs ha)).mp hzero)
      · exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
          (isCompact_sphere z r)).mp (hconv.mono (Set.subset_univ _))
      · exact hconv.tendsto_at (Set.mem_univ z)
    exact hn he
  · rintro ⟨n, rfl⟩
    exact entireSingleSpectralProduct_root hp ξ hξ n

/-- A complete critical labeling gives exactly the discriminant derivative's zero set. -/
theorem CriticalPointLabeling.product_eq_zero_iff (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) (N : ℕ) (ξ : ℤ → ℂ)
    (h : CriticalPointLabeling hp hp1 φ hφ N ξ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p) (z : ℂ) :
    entireSingleSpectralProduct ξ z = 0 ↔ deriv (canonicalDiscriminant hp φ) z = 0 := by
  have hrange : Set.range ξ = {z | deriv (canonicalDiscriminant hp φ) z = 0} := by
    ext z
    exact (h.exhaustive z).symm
  have hc : IsClosed (Set.range ξ) := by
    rw [hrange]
    exact isClosed_eq
      (continuousOn_univ.mp (analyticOnNhd_discriminant_derivative hp hp1 φ hφ).continuousOn)
      continuous_const
  exact (entireSingleSpectralProduct_eq_zero_iff hp ξ hξ hc z).trans (h.exhaustive z).symm

/-- Every even finite-p potential has an entire critical product with the exact critical zero set. -/
theorem exists_entire_criticalPointProduct (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) :
    ∃ N : ℕ, ∃ ξ : ℤ → ℂ, CriticalPointLabeling hp hp1 φ hφ N ξ ∧
      Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p ∧
      AnalyticOnNhd ℂ (entireSingleSpectralProduct ξ) Set.univ ∧
      (∀ z, entireSingleSpectralProduct ξ z = 0 ↔ deriv (canonicalDiscriminant hp φ) z = 0) := by
  obtain ⟨N,ξ,h,hξ⟩ := exists_criticalPointLabeling_memℓp hp hp1 φ hφ
  exact ⟨N,ξ,h,hξ,analyticOnNhd_entireSingleSpectralProduct hp ξ hξ,
    h.product_eq_zero_iff hp hp1 φ hφ N ξ hξ⟩

end NLS.ZakharovShabat
