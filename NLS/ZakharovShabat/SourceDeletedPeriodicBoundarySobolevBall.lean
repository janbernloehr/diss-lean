import NLS.ZakharovShabat.SourceDeletedPeriodicDiscSobolevBall
import NLS.ZakharovShabat.SourceDeletedPeriodicBoundaryError

/-! # Uniform deleted-product boundary errors

The deleted periodic product normalization estimate holds at both canonical boundary sequences throughout each real Sobolev ball.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Both canonical boundary sequences have the uniform deleted-product
normalization error on every real original Hs ball. -/
theorem exists_uniform_real_higherSobolev_deleted_product_boundary_error_bound
    (s : ℕ) (hs : 1 ≤ s) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ ab : realTypeHigherSobolevSourceLocus s, ‖ab.val‖ ≤ R → ∀ θ : BoundaryCondition,
      ∀ n : ℤ, K ≤ n.natAbs →
      ‖canonicalDeletedPeriodicProduct (by norm_num) (by norm_num)
        (periodOnePotential (higherSobolevSourceInclusion s ab.val)) (periodOnePotential_mem _) n
        (canonicalPeriodOneBoundaryRoots (by norm_num) (by norm_num) θ
          (higherSobolevSourceInclusion s ab.val) n)-1‖ ≤ C/(1+|(n:ℝ)|) := by
  obtain ⟨K,hK,C,hC,hdisc⟩ := exists_uniform_real_higherSobolev_deleted_product_disc_error_bound s hs R hR
  obtain ⟨_,M,_,hM,hboundary⟩ := exists_uniform_real_higherSobolev_displacement_envelopes s hs R hR
  obtain ⟨B,hB,hfree⟩ := exists_freeSquaredSine_displacement_bounds 1
  obtain ⟨L,hL⟩ := exists_nat_ge M
  refine ⟨max K L,hK.trans_le (le_max_left _ _),C+B*M,by positivity,?_⟩
  intro ab hab θ n hn
  let μ := canonicalPeriodOneBoundaryRoots (by norm_num) (by norm_num) θ
    (higherSobolevSourceInclusion s ab.val) n
  let q : ℝ := 1+|(n:ℝ)|
  have hq : 0 < q := by dsimp [q]; positivity
  have hμ : ‖μ-(Real.pi:ℂ)*n‖ ≤ M/q := by
    apply (le_div_iff₀ hq).mpr
    simpa only [sourceBoundaryDisplacement_apply,μ,q,mul_comm] using ((hboundary ab hab).1 θ).2 n
  have hμ1 : ‖μ-(Real.pi:ℂ)*n‖ ≤ 1 := hμ.trans (by
    apply (div_le_one hq).mpr
    have hnL : (L:ℝ) ≤ (n.natAbs:ℝ) := by exact_mod_cast (le_max_right K L).trans hn
    have habs : |(n:ℝ)| = (n.natAbs:ℝ) := by simp
    dsimp only [q]
    rw [habs]
    linarith)
  have hd := hdisc ab hab n ((le_max_left _ _).trans hn) μ hμ1
  have hf := (hfree n μ hμ1).1.trans (mul_le_mul_of_nonneg_left hμ hB)
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (canonicalDeletedPeriodicProduct (by norm_num) (by norm_num)
      (periodOnePotential (higherSobolevSourceInclusion s ab.val)) (periodOnePotential_mem _) n μ)
    ((freeSineQuotient n μ)^2) 1
  exact ht.trans ((add_le_add hd hf).trans_eq (by dsimp only [q]; ring))

end NLS.ZakharovShabat
