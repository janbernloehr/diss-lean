import NLS.ZakharovShabat.BoundaryCharacteristicProducts
import NLS.ZakharovShabat.RelativeSpectralProductsFamilies
import NLS.ComplexAnalysis.UniformEntireFamilies

/-!
# Uniform convergence for bounded families of full single products
Hölder tails control relative products off the free lattice. Multiplication
by the free sine product and maximum modulus give uniform convergence on
every compact spectral set, without continuity of the family of root labels.
-/

noncomputable section
open Set Filter Topology Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Full single products converge uniformly near each nonfree point over any bounded displacement family. -/
theorem tendstoUniformlyOn_singleSpectralProduct_halfGap {X : Type*} (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ξ : X → ℤ → ℂ) (hξ : ∀ x, Memℓp (fun n => ξ x n-(Real.pi : ℂ)*n) p)
    (S : Set X) (R : ℝ) (hR : 0 ≤ R) (hb : ∀ x ∈ S, ‖(⟨_,hξ x⟩ : Coeff p)‖ ≤ R)
    (z₀ : ℂ) (hz₀ : z₀ ∉ freeLattice) :
    TendstoUniformlyOn (fun N (t : ℂ × X) => singleSpectralPartialProduct (ξ t.2) t.1 N)
      (fun t => singleSpectralProductFormula (ξ t.2) t.1) atTop (closedBall z₀ (freeGap z₀/2) ×ˢ S) := by
  let K := closedBall z₀ (freeGap z₀/2)
  let T : Set (ℂ × X) := K ×ˢ S
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKl : K ⊆ freeLatticeᶜ := closedBall_half_freeGap_subset z₀ hz₀
  obtain ⟨B,hB,hbound,hC⟩ := uniformCauchySeqOn_spectralRelativeFactor_family hp hp1 ξ hξ S R hR hb z₀ hz₀
  have hrel := hC.tendstoUniformlyOn_of_tendsto (fun t ht =>
    (tendstoLocallyUniformlyOn_spectralRelativeProduct hp (ξ t.2) (hξ t.2)).tendsto_at (hKl ht.1))
  have hrelB (t : ℂ × X) (ht : t ∈ T) : ‖∏' n, spectralRelativeFactor (ξ t.2) t.1 n‖ ≤ B := by
    apply le_of_tendsto ((tendstoLocallyUniformlyOn_spectralRelativeProduct hp (ξ t.2) (hξ t.2)).tendsto_at (hKl ht.1)).norm
    exact Filter.Eventually.of_forall (fun N => hbound N t ht)
  have hfree := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    (tendstoLocallyUniformlyOn_singleSpectralPartialProduct_free.mono (subset_univ K))
  have hfreeLift := (hfree.comp (Prod.fst : ℂ × X → ℂ)).mono
    (show T ⊆ Prod.fst ⁻¹' K from fun _ ht => ht.1)
  have hcont : ContinuousOn (fun z : ℂ => -2*Complex.sin z) K := by fun_prop
  obtain ⟨A,hAb⟩ := hK.exists_bound_of_continuousOn hcont
  have hprod := NLS.ComplexAnalysis.tendstoUniformlyOn_mul_bounded _ _ _ _ T (max A 0) B
    (le_max_right _ _) hB hfreeLift hrel
    (fun t ht => (hAb t.1 ht.1).trans (le_max_left _ _)) hrelB
  apply hprod.congr
  exact Filter.Eventually.of_forall (fun N t ht =>
    (singleSpectralPartialProduct_eq (ξ t.2) t.1 (hKl ht.1) N).symm)

/-- Bounded full displacements give uniform convergence on all spectral compacts, including free centers. -/
theorem tendstoUniformlyOn_entireSingleSpectralProduct_family {X : Type*} (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ξ : X → ℤ → ℂ) (hξ : ∀ x, Memℓp (fun n => ξ x n-(Real.pi : ℂ)*n) p)
    (S : Set X) (R : ℝ) (hR : 0 ≤ R) (hb : ∀ x ∈ S, ‖(⟨_,hξ x⟩ : Coeff p)‖ ≤ R)
    (K : Set ℂ) (hK : IsCompact K) :
    TendstoUniformlyOn (fun N (t : ℂ × X) => singleSpectralPartialProduct (ξ t.2) t.1 N)
      (fun t => entireSingleSpectralProduct (ξ t.2) t.1) atTop (K ×ˢ S) := by
  let F (N : ℕ) (t : ℂ × X) := singleSpectralPartialProduct (ξ t.2) t.1 N
  have hlocal : ∀ z ∉ freeLattice, ∃ V ∈ 𝓝 z, UniformCauchySeqOn F atTop (V ×ˢ S) := by
    intro z hz
    exact ⟨closedBall z (freeGap z/2),closedBall_mem_nhds z (half_pos (freeGap_pos hz)),
      (tendstoUniformlyOn_singleSpectralProduct_halfGap hp hp1 ξ hξ S R hR hb z hz).uniformCauchySeqOn⟩
  have hC := NLS.ComplexAnalysis.uniformCauchySeqOn_compact_prod_of_countable F S
    (fun N x z => (analyticOnNhd_singleSpectralPartialProduct (ξ x) N z (mem_univ z)).differentiableAt)
    freeLattice countable_freeLattice hlocal K hK
  exact hC.tendstoUniformlyOn_of_tendsto (fun t _ =>
    (tendstoLocallyUniformlyOn_entireSingleSpectralProduct hp (ξ t.2) (hξ t.2)).tendsto_at (mem_univ t.1))

/-- The source-normalized boundary products inherit convergence uniform over bounded root families. -/
theorem tendstoUniformlyOn_boundaryCharacteristicProduct_family {X : Type*} (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ξ : X → ℤ → ℂ) (hξ : ∀ x, Memℓp (fun n => ξ x n-(Real.pi : ℂ)*n) p)
    (S : Set X) (R : ℝ) (hR : 0 ≤ R) (hb : ∀ x ∈ S, ‖(⟨_,hξ x⟩ : Coeff p)‖ ≤ R)
    (K : Set ℂ) (hK : IsCompact K) :
    TendstoUniformlyOn (fun N (t : ℂ × X) => boundaryCharacteristicPartialProduct (ξ t.2) t.1 N)
      (fun t => boundaryCharacteristicProduct (ξ t.2) t.1) atTop (K ×ˢ S) := by
  have h := tendstoUniformlyOn_entireSingleSpectralProduct_family hp hp1 ξ hξ S R hR hb K hK
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with N hN t ht
  have hd := hN t ht
  rw [dist_eq_norm] at hd
  rw [boundaryCharacteristicPartialProduct_eq,boundaryCharacteristicProduct,dist_eq_norm,← mul_sub,norm_mul]
  norm_num only [norm_div,norm_neg,norm_one,Complex.norm_ofNat]
  linarith [norm_nonneg (entireSingleSpectralProduct (ξ t.2) t.1-singleSpectralPartialProduct (ξ t.2) t.1 N)]

end NLS.ZakharovShabat
