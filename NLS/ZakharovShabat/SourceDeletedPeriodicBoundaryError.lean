import NLS.ZakharovShabat.SourceDeletedPeriodicDiscError
import NLS.ZakharovShabat.SourceBoundaryWeightedDisplacement
import NLS.ZakharovShabat.FreeSquaredSineBounds

/-! # Deleted periodic products at actual boundary roots

Both canonical boundary sequences give an inverse-index deleted-product normalization error on original complex Sobolev neighborhoods.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- At either canonical boundary sequence, the actual deleted periodic
product differs from one by a locally uniform inverse-index error on
original Hs neighborhoods. This includes complex sources and requires
no smooth representative. -/
theorem exists_local_higherSobolev_deleted_product_boundary_error_bound
    (s : ℕ) (hs : 1 ≤ s) (a₀ : realTypeHigherSobolevSourceLocus s) (θ : BoundaryCondition) :
    ∃ U : Set (SobolevSource s), IsOpen U ∧ a₀.val ∈ U ∧
      ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ ab ∈ U,
      ∀ n : ℤ, K ≤ n.natAbs →
        ‖canonicalDeletedPeriodicProduct (by norm_num) (by norm_num)
          (periodOnePotential (higherSobolevSourceInclusion s ab)) (periodOnePotential_mem _) n
          (canonicalPeriodOneBoundaryRoots (by norm_num) (by norm_num) θ
            (higherSobolevSourceInclusion s ab) n)-1‖ ≤ C/(1+|(n:ℝ)|) := by
  obtain ⟨Ud,hUd,had,K,hK,C,hC,hdisc⟩ :=
    exists_local_higherSobolev_deleted_product_disc_error_bound s hs a₀
  obtain ⟨Ub,hUb,hab,_,_,M,_,_,hM,hboundary⟩ :=
    exists_local_higherSobolev_boundary_weighted_displacement_bounds s hs a₀ θ
  obtain ⟨B,hB,hfree⟩ := exists_freeSquaredSine_displacement_bounds 1
  obtain ⟨L,hL⟩ := exists_nat_ge M
  refine ⟨Ud ∩ Ub,hUd.inter hUb,⟨had,hab⟩,max K L,hK.trans_le (le_max_left _ _),
    C+B*M,by positivity,?_⟩
  intro ab hab n hn
  let μ := canonicalPeriodOneBoundaryRoots (by norm_num) (by norm_num) θ
    (higherSobolevSourceInclusion s ab) n
  let q : ℝ := 1+|(n:ℝ)|
  have hq : 0 < q := by dsimp [q]; positivity
  have hμ : ‖μ-(Real.pi:ℂ)*n‖ ≤ M/q := by
    apply (le_div_iff₀ hq).mpr
    simpa only [sourceBoundaryDisplacement_apply,μ,q,mul_comm] using (hboundary ab hab.2).2.2 n
  have hμ1 : ‖μ-(Real.pi:ℂ)*n‖ ≤ 1 := hμ.trans (by
    apply (div_le_one hq).mpr
    have hnL : (L:ℝ) ≤ (n.natAbs:ℝ) := by exact_mod_cast (le_max_right K L).trans hn
    have habs : |(n:ℝ)| = (n.natAbs:ℝ) := by simp
    dsimp only [q]
    rw [habs]
    linarith)
  have hd := hdisc ab hab.1 n ((le_max_left _ _).trans hn) μ hμ1
  have hf := (hfree n μ hμ1).1.trans (mul_le_mul_of_nonneg_left hμ hB)
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (canonicalDeletedPeriodicProduct (by norm_num) (by norm_num)
      (periodOnePotential (higherSobolevSourceInclusion s ab)) (periodOnePotential_mem _) n μ)
    ((freeSineQuotient n μ)^2) 1
  exact ht.trans ((add_le_add hd hf).trans_eq (by dsimp only [q]; ring))

end NLS.ZakharovShabat
