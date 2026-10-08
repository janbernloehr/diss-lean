import NLS.ZakharovShabat.AppendixDSineProducts
import NLS.ZakharovShabat.AppendixDRelativeProductBounds

/-! # The deleted-product identity used in Lemma D.8

The source's positive product divided by pi_n is the existing joint deleted
product. Factoring its literal finite cutoffs against the free cutoffs proves
the sine identity on the entire disc, including the removable center.
-/
noncomputable section
open Set Filter Topology Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The free reference lattice meets D.6's separation hypothesis on every source disc. -/
theorem appendixD_freeReferenceSeparated : AppendixDReferenceSeparated (0:Coeff ⊤) 1 0 := by
  intro n _ z hz m hmn
  have hm : (Real.pi:ℂ)*m ∈ refinedResonantDisk m := by
    simp only [refinedResonantDisk,mem_ball,dist_self]
    positivity
  have h := (refinedResonantDisk_pointwise_separation hmn hm hz).1
  rw [dist_eq_norm] at h
  have hπ : 1 ≤ Real.pi/2 := by nlinarith [Real.pi_gt_three]
  simp only [inv_one,one_mul,displacedRoots,lp.coeFn_zero,Pi.zero_apply,add_zero]
  nlinarith [abs_nonneg (((m-n:ℤ):ℝ))]

/-- D.8's literal positive symmetric product, with its displayed denominator pi_n. -/
theorem tendsto_appendixDNormalizedDeletedProduct (hp : p ≠ ⊤) (n : ℤ) (t : ℂ × Coeff p) :
    Tendsto (fun M : ℕ => (1/singleSpectralDenominator n)*
      ∏ m ∈ (Finset.Icc (-(M:ℤ)) (M:ℤ)).erase n,
        (displacedRoots t.2 m-t.1)/singleSpectralDenominator m) atTop
      (𝓝 (jointDeletedSingleSpectralProduct n t)) := by
  have h := (tendstoUniformlyOn_jointDeletedSingleSpectralProduct_finite hp n
    {t.1} isCompact_singleton {t.2} ‖t.2‖ (norm_nonneg _)
    (by rintro a (rfl : a = t.2); exact le_rfl)).tendsto_at
      (show t ∈ ({t.1}:Set ℂ) ×ˢ {t.2} from ⟨rfl,rfl⟩)
  simpa only [jointDeletedSingleSpectralPartialProduct,singleSpectralFactor,
    one_div,div_eq_mul_inv,mul_comm,one_mul] using h

/-- Factoring against the free product gives the exact multiplicative identity on every disc. -/
theorem appendixDDeletedProduct_eq_free_mul_relative (hp1 : 1 < p) (hp : p ≠ ⊤)
    (a : Coeff p) (n : ℤ) (z : ℂ) (hz : z ∈ refinedResonantDisk n) :
    jointDeletedSingleSpectralProduct n (z,a) =
      freeSineQuotient n z*(1+appendixDRelativeProductError (0:Coeff ⊤) a n z) := by
  classical
  let f : ℤ → ℂ := fun m => if m = n then 1 else
    (displacedRoots (0:Coeff ⊤) m+a m-z)/(displacedRoots (0:Coeff ⊤) m-z)
  have hf := multipliable_appendixDRelativeProduct hp1 hp (0:Coeff ⊤) a
    (by norm_num) appendixD_freeReferenceSeparated (Nat.zero_le _) hz
  have hrelative : Tendsto (fun M : ℕ => ∏ m ∈ Finset.Icc (-(M:ℤ)) (M:ℤ), f m) atTop
      (𝓝 (∏' m, f m)) := hf.hasProd.comp Finset.tendsto_Icc_neg
  have hfree := tendsto_appendixDNormalizedDeletedProduct hp n (z,(0:Coeff p))
  rw [congrFun (jointDeletedSingleSpectralProduct_zero_eq_freeSineQuotient hp hp1 n) z] at hfree
  have ha := tendsto_appendixDNormalizedDeletedProduct hp n (z,a)
  have hfinite (M : ℕ) :
      (1/singleSpectralDenominator n)*
        (∏ m ∈ (Finset.Icc (-(M:ℤ)) (M:ℤ)).erase n,
          (displacedRoots (0:Coeff p) m-z)/singleSpectralDenominator m)*
        (∏ m ∈ Finset.Icc (-(M:ℤ)) (M:ℤ), f m) =
      (1/singleSpectralDenominator n)*
        ∏ m ∈ (Finset.Icc (-(M:ℤ)) (M:ℤ)).erase n,
          (displacedRoots a m-z)/singleSpectralDenominator m := by
    rw [← Finset.prod_erase (Finset.Icc (-(M:ℤ)) (M:ℤ)) (by simp [f] : f n = 1),
      mul_assoc,← Finset.prod_mul_distrib]
    congr 1
    apply Finset.prod_congr rfl
    intro m hm
    have hmn := Finset.ne_of_mem_erase hm
    have hd := appendixD_reference_denominator_ne_zero (0:Coeff ⊤)
      (by norm_num) appendixD_freeReferenceSeparated (Nat.zero_le _) hmn hz
    simp only [displacedRoots,lp.coeFn_zero,Pi.zero_apply,add_zero] at hd
    simp only [f,if_neg hmn,displacedRoots,lp.coeFn_zero,Pi.zero_apply,add_zero]
    field_simp
  have he := tendsto_nhds_unique ((hfree.mul hrelative).congr' (Eventually.of_forall hfinite)) ha
  have hprod : (∏' m, f m) = 1+appendixDRelativeProductError (0:Coeff ⊤) a n z := by
    unfold appendixDRelativeProductError
    change _ = 1+((∏' m, f m)-1)
    ring
  rw [hprod] at he
  exact he.symm

/-- The additive error in D.8 is the free sine quotient times the same relative error. -/
theorem appendixDDeletedProduct_sub_free_eq (hp1 : 1 < p) (hp : p ≠ ⊤)
    (a : Coeff p) (n : ℤ) (z : ℂ) (hz : z ∈ refinedResonantDisk n) :
    jointDeletedSingleSpectralProduct n (z,a)-freeSineQuotient n z =
      freeSineQuotient n z*appendixDRelativeProductError (0:Coeff ⊤) a n z := by
  rw [appendixDDeletedProduct_eq_free_mul_relative hp1 hp a n z hz]
  ring

end NLS.ZakharovShabat
