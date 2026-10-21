import NLS.ZakharovShabat.SourcePeriodicDisplacementSobolevBall
import NLS.ZakharovShabat.SourceDeletedPeriodicDiscError

/-! # Uniform deleted-product disc errors

The actual deleted periodic products have a common inverse-index error on distant unit discs throughout each real Sobolev ball.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The actual deleted periodic product has a common inverse-index error
on distant unit discs over each entire real original Hs ball. -/
theorem exists_uniform_real_higherSobolev_deleted_product_disc_error_bound
    (s : ℕ) (hs : 1 ≤ s) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ ab : realTypeHigherSobolevSourceLocus s, ‖ab.val‖ ≤ R →
      ∀ n : ℤ, K ≤ n.natAbs → ∀ z : ℂ, ‖z-(Real.pi:ℂ)*n‖ ≤ 1 →
      ‖canonicalDeletedPeriodicProduct (by norm_num) (by norm_num)
        (periodOnePotential (higherSobolevSourceInclusion s ab.val)) (periodOnePotential_mem _) n z-
        (freeSineQuotient n z)^2‖ ≤ C/(1+|(n:ℝ)|) := by
  obtain ⟨M,hM,hend⟩ := exists_uniform_real_higherSobolev_periodic_displacement_bound s hs R hR
  obtain ⟨A,hA,htrace⟩ := exists_uniform_higherSobolev_discriminant_sq_free_strip_bound s hs R 1 hR
  obtain ⟨B,hB,hfree⟩ := exists_bound_freeSineQuotient 1
  obtain ⟨K₀,hK₀,hfreq⟩ := exists_wkb_bounded_frequency_cutoff 1 zero_le_one
  obtain ⟨L,hL⟩ := exists_nat_ge (2*M)
  refine ⟨max K₀ L,hK₀.trans_le (le_max_left _ _),A+8*B^2*M+4*B^2*M^2,by positivity,?_⟩
  intro ab hab n hn z hz
  have habend := hend ab hab
  let q : ℝ := 1+|(n:ℝ)|
  let ε : ℝ := M/q
  have hq : 1 ≤ q := by dsimp [q]; linarith [abs_nonneg (n:ℝ)]
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hMhalf : ε ≤ 1/2 := by
    have hnL : (L:ℝ) ≤ (n.natAbs:ℝ) := by exact_mod_cast (le_max_right K₀ L).trans hn
    have habs : |(n:ℝ)| = (n.natAbs:ℝ) := by simp
    dsimp only [ε]
    apply (div_le_iff₀ hqpos).mpr
    dsimp only [q]
    rw [habs]
    linarith
  have hε : 0 ≤ ε := div_nonneg hM hqpos.le
  have hleft : ‖canonicalPeriodicLeft (by norm_num) (by norm_num)
      (periodOnePotential (higherSobolevSourceInclusion s ab.val)) (periodOnePotential_mem _) n-(Real.pi:ℂ)*n‖ ≤ ε := by
    apply (le_div_iff₀ hqpos).mpr
    simpa only [q,mul_comm] using (habend n).1
  have hright : ‖canonicalPeriodicRight (by norm_num) (by norm_num)
      (periodOnePotential (higherSobolevSourceInclusion s ab.val)) (periodOnePotential_mem _) n-(Real.pi:ℂ)*n‖ ≤ ε := by
    apply (le_div_iff₀ hqpos).mpr
    simpa only [q,mul_comm] using (habend n).2
  have hcircle (w : ℂ) (hw : w ∈ sphere ((Real.pi:ℂ)*n) 1) :
      ‖(canonicalDiscriminant (by norm_num) (periodOnePotential (higherSobolevSourceInclusion s ab.val)) w)^2-
        (freeDiscriminant w)^2‖ ≤ A/q := by
    have hwr : ‖w-(Real.pi:ℂ)*n‖ = 1 := by simpa only [mem_sphere,dist_eq_norm] using hw
    have hg := hfreq (fun _ => w-(Real.pi:ℂ)*n) (fun _ => hwr.le) n ((le_max_left _ _).trans hn)
    simp only [add_sub_cancel] at hg
    have him : |w.im| ≤ 1 := by
      have hi := abs_im_le_norm (w-(Real.pi:ℂ)*n)
      simpa [hwr,Complex.mul_im] using hi
    exact (htrace ab.val hab w hg.1 him).trans (div_le_div_of_nonneg_left hA hqpos hg.2)
  have hm (w : ℂ) (hw : w ∈ sphere ((Real.pi:ℂ)*n) 1) : ‖(freeSineQuotient n w)^2‖ ≤ B^2 := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hfree n w (le_of_eq (by simpa only [mem_sphere,dist_eq_norm] using hw))) 2
  have h := norm_canonicalDeletedPeriodicProduct_sub_free_on_closedDisc
    (by norm_num) (by norm_num) _ (periodOnePotential_mem _) n 1 ε (A/q) (B^2)
    zero_lt_one hε hMhalf (sq_nonneg B) hleft hright hcircle hm z hz
  apply h.trans
  simp only [one_pow,div_one,mul_one]
  apply (le_div_iff₀ hqpos).mpr
  have hεq : ε*q = M := div_mul_cancel₀ M hqpos.ne'
  have hεM : ε ≤ M := div_le_self hM hq
  have hsq : ε^2*q ≤ M^2 := by nlinarith [mul_le_mul_of_nonneg_left hεM hM]
  have hquad := mul_le_mul_of_nonneg_left hsq (sq_nonneg B)
  have hAq : (A/q)*q = A := div_mul_cancel₀ A hqpos.ne'
  nlinarith

end NLS.ZakharovShabat
