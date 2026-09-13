import NLS.ZakharovShabat.CanonicalPeriodicProductUniform
import NLS.ZakharovShabat.EntireSpectralPairProducts

/-!
# Entire paired products uniform over bounded displacement families

The relative-product estimates and maximum modulus extend uniform convergence
across the free lattice, with a common compact-set bound on the entire limits.
The parameter family need not carry a topology or continuous root labels.
-/

noncomputable section
open Filter Topology Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Complete paired cutoffs converge uniformly over bounded displacement families on every spectral compact set. -/
theorem tendstoUniformlyOn_entireSpectralPairProduct_family {X : Type*}
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ξ η : X → ℤ → ℂ)
    (hξ : ∀ x, Memℓp (fun n => ξ x n-(Real.pi : ℂ)*n) p)
    (hη : ∀ x, Memℓp (fun n => η x n-(Real.pi : ℂ)*n) p)
    (R : ℝ) (hR : 0 ≤ R) (hbξ : ∀ x, ‖(⟨_,hξ x⟩ : Coeff p)‖ ≤ R)
    (hbη : ∀ x, ‖(⟨_,hη x⟩ : Coeff p)‖ ≤ R) (K : Set ℂ) (hK : IsCompact K) :
    TendstoUniformlyOn (fun (M : ℕ) (t : ℂ × X) => spectralPairPartialProduct (ξ t.2) (η t.2) t.1 M)
      (fun t => entireSpectralPairProduct (ξ t.2) (η t.2) t.1) atTop (K ×ˢ Set.univ) := by
  let F (M : ℕ) (t : ℂ × X) := spectralPairPartialProduct (ξ t.2) (η t.2) t.1 M
  have hlocal : ∀ z ∉ freeLattice, ∃ V ∈ 𝓝 z, UniformCauchySeqOn F atTop (V ×ˢ Set.univ) := by
    intro z hz
    let V := closedBall z (freeGap z/2)
    have hV : IsCompact V := isCompact_closedBall _ _
    have hrel := tendstoUniformlyOn_spectralRelativePair_family hp hp1 ξ η hξ hη Set.univ R hR
      (fun x _ => hbξ x) (fun x _ => hbη x) z hz
    obtain ⟨B,hB,hBb⟩ := exists_bound_spectralRelativePair_family hp hp1 ξ η hξ hη R hR hbξ hbη z hz
    have hfree := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hV).mp
      (tendstoLocallyUniformlyOn_freePeriodicFullProduct.mono (Set.subset_univ V))
    have hfreeLift := (hfree.comp (Prod.fst : ℂ × X → ℂ)).mono
      (show V ×ˢ (Set.univ : Set X) ⊆ Prod.fst ⁻¹' V from fun _ ht => ht.1)
    have hcont : ContinuousOn (fun z : ℂ => freeDiscriminant z^2-4) V := by
      unfold freeDiscriminant
      fun_prop
    obtain ⟨A,hAb⟩ := hV.exists_bound_of_continuousOn hcont
    have hprod := NLS.ComplexAnalysis.tendstoUniformlyOn_mul_bounded _ _ _ _ (V ×ˢ Set.univ)
      (max A 0) B (le_max_right _ _) hB hfreeLift hrel
      (fun t ht => (hAb t.1 ht.1).trans (le_max_left _ _)) hBb
    refine ⟨V,closedBall_mem_nhds z (half_pos (freeGap_pos hz)),?_⟩
    apply (hprod.congr ?_).uniformCauchySeqOn
    exact Filter.Eventually.of_forall (fun M t ht =>
      (spectralPairPartialProduct_eq (ξ t.2) (η t.2) t.1 (closedBall_half_freeGap_subset z hz ht.1) M).symm)
  have hC := NLS.ComplexAnalysis.uniformCauchySeqOn_compact_prod_of_countable F Set.univ
    (fun M x z => (analyticOnNhd_spectralPairPartialProduct (ξ x) (η x) M z (Set.mem_univ z)).differentiableAt)
    freeLattice countable_freeLattice hlocal K hK
  exact hC.tendstoUniformlyOn_of_tendsto (fun t _ =>
    (tendstoLocallyUniformlyOn_entireSpectralPairProduct hp (ξ t.2) (η t.2) (hξ t.2) (hη t.2)).tendsto_at
      (Set.mem_univ t.1))

/-- Every fixed cutoff is uniformly bounded on compact spectral sets over a bounded displacement family. -/
theorem exists_bound_spectralPairPartialProduct_family {X : Type*}
    (ξ η : X → ℤ → ℂ) (hξ : ∀ x, Memℓp (fun n => ξ x n-(Real.pi : ℂ)*n) p)
    (hη : ∀ x, Memℓp (fun n => η x n-(Real.pi : ℂ)*n) p)
    (R : ℝ) (hR : 0 ≤ R) (hbξ : ∀ x, ‖(⟨_,hξ x⟩ : Coeff p)‖ ≤ R)
    (hbη : ∀ x, ‖(⟨_,hη x⟩ : Coeff p)‖ ≤ R) (K : Set ℂ) (hK : IsCompact K) (M : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ K ×ˢ (Set.univ : Set X),
      ‖spectralPairPartialProduct (ξ t.2) (η t.2) t.1 M‖ ≤ B := by
  obtain ⟨A,hA,hAb⟩ := hK.isBounded.exists_pos_norm_le
  let b (n : ℤ) : ℝ := (R+‖(Real.pi : ℂ)*n‖+A)^2/‖spectralPairDenominator n‖
  have hb (n : ℤ) : 0 ≤ b n := by dsimp [b]; positivity
  refine ⟨4*∏ n ∈ Finset.Icc (-(M : ℤ)) M, b n, by positivity, ?_⟩
  intro t ht
  have hroot (α : ℤ → ℂ) (hα : Memℓp (fun n => α n-(Real.pi : ℂ)*n) p)
      (hbound : ‖(⟨_,hα⟩ : Coeff p)‖ ≤ R) (n : ℤ) :
      ‖α n-t.1‖ ≤ R+‖(Real.pi : ℂ)*n‖+A := by
    have hn := (lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
      (⟨_,hα⟩ : Coeff p) n).trans hbound
    have he := norm_le_norm_sub_add (α n) ((Real.pi : ℂ)*n)
    have hz := hAb t.1 ht.1
    have hd := norm_sub_le (α n) t.1
    dsimp at hn
    linarith
  rw [spectralPairPartialProduct, norm_mul]
  norm_num only [norm_neg, Complex.norm_ofNat]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply (Finset.norm_prod_le _ _).trans
  apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
  intro n _
  rw [spectralPairFactor_eq_div, norm_div, norm_mul]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  simpa only [pow_two] using mul_le_mul (hroot (ξ t.2) (hξ t.2) (hbξ t.2) n)
    (hroot (η t.2) (hη t.2) (hbη t.2) n) (norm_nonneg _) (by positivity)

/-- Entire limits have one bound over the whole displacement family on each spectral compact set. -/
theorem exists_bound_entireSpectralPairProduct_family {X : Type*}
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ξ η : X → ℤ → ℂ)
    (hξ : ∀ x, Memℓp (fun n => ξ x n-(Real.pi : ℂ)*n) p)
    (hη : ∀ x, Memℓp (fun n => η x n-(Real.pi : ℂ)*n) p)
    (R : ℝ) (hR : 0 ≤ R) (hbξ : ∀ x, ‖(⟨_,hξ x⟩ : Coeff p)‖ ≤ R)
    (hbη : ∀ x, ‖(⟨_,hη x⟩ : Coeff p)‖ ≤ R) (K : Set ℂ) (hK : IsCompact K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ K ×ˢ (Set.univ : Set X),
      ‖entireSpectralPairProduct (ξ t.2) (η t.2) t.1‖ ≤ B := by
  have ht := tendstoUniformlyOn_entireSpectralPairProduct_family hp hp1 ξ η hξ hη R hR hbξ hbη K hK
  obtain ⟨M,hM⟩ := (Metric.tendstoUniformlyOn_iff.mp ht 1 (by norm_num)).exists
  obtain ⟨B,hB,hBb⟩ := exists_bound_spectralPairPartialProduct_family ξ η hξ hη R hR hbξ hbη K hK M
  refine ⟨1+B,by positivity,fun t ht => ?_⟩
  have hn := norm_le_norm_sub_add (entireSpectralPairProduct (ξ t.2) (η t.2) t.1)
    (spectralPairPartialProduct (ξ t.2) (η t.2) t.1 M)
  have hd : ‖entireSpectralPairProduct (ξ t.2) (η t.2) t.1-
      spectralPairPartialProduct (ξ t.2) (η t.2) t.1 M‖ < 1 := by
    simpa only [dist_eq_norm] using hM t ht
  linarith [hBb t ht]

end NLS.ZakharovShabat
