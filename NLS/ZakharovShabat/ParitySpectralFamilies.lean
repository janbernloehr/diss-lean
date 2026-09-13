import NLS.ZakharovShabat.EntireSpectralPairFamilies
import NLS.ZakharovShabat.ParitySpectralProducts

/-!
# Uniform entire parity products over bounded displacement families

Affine parity sampling preserves a common displacement bound. The generic
whole-plane family theorem then applies to both literal parity cutoffs,
including the scalar normalization of the asymmetric odd cutoff.
-/

noncomputable section
open Filter Topology Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Sampling and rescaling a parity does not increase the displacement norm. -/
theorem norm_parityRescale_displacement_le (hp : p ≠ ⊤) (ξ : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p) (j : ℤ) :
    ‖(⟨_,memℓp_parityRescale hp ξ hξ j⟩ : Coeff p)‖ ≤ ‖(⟨_,hξ⟩ : Coeff p)‖ := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp
  have hi : Function.Injective (fun n : ℤ => 2*n+j) := by intro a b h; dsimp at h; omega
  have hn (n : ℤ) : ‖parityRescale ξ j n-(Real.pi : ℂ)*n‖ ≤
      ‖ξ (2*n+j)-(Real.pi : ℂ)*((2*n+j : ℤ) : ℂ)‖ := by
    have he : parityRescale ξ j n-(Real.pi : ℂ)*n =
        (ξ (2*n+j)-(Real.pi : ℂ)*((2*n+j : ℤ) : ℂ))/2 := by
      unfold parityRescale
      push_cast
      ring
    rw [he, norm_div]
    norm_num only [Complex.norm_ofNat]
    exact div_le_self (norm_nonneg _) (by norm_num)
  apply lp.norm_le_of_forall_sum_le hp0 (norm_nonneg _)
  intro s
  calc
    _ ≤ ∑ n ∈ s, ‖ξ (2*n+j)-(Real.pi : ℂ)*((2*n+j : ℤ) : ℂ)‖^p.toReal := by
      exact Finset.sum_le_sum (fun n _ => Real.rpow_le_rpow (norm_nonneg _) (hn n) hp0.le)
    _ = ∑ n ∈ s.image (fun n : ℤ => 2*n+j), ‖ξ n-(Real.pi : ℂ)*n‖^p.toReal := by
      rw [Finset.sum_image (fun a _ b _ hab => hi hab)]
    _ ≤ _ := lp.sum_rpow_le_norm_rpow hp0 (⟨_,hξ⟩ : Coeff p) _

/-- Both entire parity products converge uniformly over bounded displacement families on every compact spectral set. -/
theorem tendstoUniformlyOn_paritySpectralProducts_family {X : Type*}
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ξ η : X → ℤ → ℂ)
    (hξ : ∀ x, Memℓp (fun n => ξ x n-(Real.pi : ℂ)*n) p)
    (hη : ∀ x, Memℓp (fun n => η x n-(Real.pi : ℂ)*n) p)
    (R : ℝ) (hR : 0 ≤ R) (hbξ : ∀ x, ‖(⟨_,hξ x⟩ : Coeff p)‖ ≤ R)
    (hbη : ∀ x, ‖(⟨_,hη x⟩ : Coeff p)‖ ≤ R) (K : Set ℂ) (hK : IsCompact K) :
    TendstoUniformlyOn (fun (M : ℕ) (t : ℂ × X) => evenSpectralPairCutoff (ξ t.2) (η t.2) t.1 M)
      (fun t => evenSpectralPairProduct (ξ t.2) (η t.2) t.1) atTop (K ×ˢ Set.univ) ∧
    TendstoUniformlyOn (fun (M : ℕ) (t : ℂ × X) => oddSpectralPairCutoff (ξ t.2) (η t.2) t.1 M)
      (fun t => oddSpectralPairProduct (ξ t.2) (η t.2) t.1) atTop (K ×ˢ Set.univ) := by
  have hbsξ (j : ℤ) (x : X) : ‖(⟨_,memℓp_parityRescale hp (ξ x) (hξ x) j⟩ : Coeff p)‖ ≤ R :=
    (norm_parityRescale_displacement_le hp (ξ x) (hξ x) j).trans (hbξ x)
  have hbsη (j : ℤ) (x : X) : ‖(⟨_,memℓp_parityRescale hp (η x) (hη x) j⟩ : Coeff p)‖ ≤ R :=
    (norm_parityRescale_displacement_le hp (η x) (hη x) j).trans (hbη x)
  have hfamily (j : ℤ) : TendstoUniformlyOn
      (fun M (t : ℂ × X) => spectralPairPartialProduct (parityRescale (ξ t.2) j)
        (parityRescale (η t.2) j) ((t.1-(Real.pi : ℂ)*j)/2) M)
      (fun t => entireSpectralPairProduct (parityRescale (ξ t.2) j)
        (parityRescale (η t.2) j) ((t.1-(Real.pi : ℂ)*j)/2)) atTop (K ×ˢ Set.univ) := by
    have ht := tendstoUniformlyOn_entireSpectralPairProduct_family hp hp1
      (fun x => parityRescale (ξ x) j) (fun x => parityRescale (η x) j)
      (fun x => memℓp_parityRescale hp (ξ x) (hξ x) j) (fun x => memℓp_parityRescale hp (η x) (hη x) j)
      R hR (hbsξ j) (hbsη j) ((fun z : ℂ => (z-(Real.pi : ℂ)*j)/2) '' K) (hK.image (by fun_prop))
    exact (ht.comp (fun t : ℂ × X => ((t.1-(Real.pi : ℂ)*j)/2,t.2))).mono
      (fun t ht => ⟨⟨t.1,ht.1,rfl⟩,Set.mem_univ _⟩)
  constructor
  · have ht := hfamily 0
    simp only [Int.cast_zero, mul_zero, sub_zero] at ht
    exact ht.congr (Filter.Eventually.of_forall (fun M t _ => (evenSpectralPairCutoff_eq _ _ _ M).symm))
  · obtain ⟨B,hB,hBb⟩ := exists_bound_entireSpectralPairProduct_family hp hp1
      (fun x => parityRescale (ξ x) 1) (fun x => parityRescale (η x) 1)
      (fun x => memℓp_parityRescale hp (ξ x) (hξ x) 1) (fun x => memℓp_parityRescale hp (η x) (hη x) 1)
      R hR (hbsξ 1) (hbsη 1) ((fun z : ℂ => (z-(Real.pi : ℂ))/2) '' K) (hK.image (by fun_prop))
    have hc := ((tendsto_const_nhds (x := (-1 : ℂ))).div tendsto_rescaledOddReference one_ne_zero).tendstoUniformlyOn_const
      (K ×ˢ (Set.univ : Set X))
    have ht := hfamily 1
    simp only [Int.cast_one, mul_one] at ht
    have hh := NLS.ComplexAnalysis.tendstoUniformlyOn_mul_bounded _ _ _ _ (K ×ˢ Set.univ) 1 B
      (by norm_num) hB hc ht (fun _ _ => by norm_num)
      (fun t ht => hBb ((t.1-(Real.pi : ℂ))/2,t.2) ⟨⟨t.1,ht.1,rfl⟩,Set.mem_univ _⟩)
    have he := hh.congr (F' := fun M t => oddSpectralPairCutoff (ξ t.2) (η t.2) t.1 M) ?_
    · simpa only [div_one, neg_one_mul, oddSpectralPairProduct] using he
    · exact Filter.Eventually.of_forall (fun M t _ => by
        dsimp only [Pi.mul_apply, Pi.div_apply, Function.comp_def]
        rw [oddSpectralPairCutoff_eq]
        ring)

end NLS.ZakharovShabat
