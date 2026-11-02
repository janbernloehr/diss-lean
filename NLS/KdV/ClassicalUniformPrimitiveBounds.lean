import NLS.KdV.ClassicalUniformRootBounds

/-! # Uniform actual primitive errors on all positive contours

The constructed primitive has a uniformly bounded source derivative on a
small potential ball. Its error from the exact free primitive is therefore
O(norm q), simultaneously on every positive fixed frequency circle.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem hasFDerivAt_classicalHillContinuedPrimitive_source (lam : ℂ)
    (q : NLS.LinearVolterra.Curve ℂ) (h : (lam,q) ∈ classicalHillContinuationDomain) :
    HasFDerivAt (fun a : NLS.LinearVolterra.Curve ℂ => classicalHillContinuedPrimitive (lam,a))
      ((classicalHillContinuedRoot (lam,q))⁻¹ •
        fderiv ℂ (fun a : NLS.LinearVolterra.Curve ℂ => classicalHillDiscriminant a lam) q) q := by
  let J := ContinuousLinearMap.inr ℂ ℂ (NLS.LinearVolterra.Curve ℂ)
  have hi : HasFDerivAt (fun a : NLS.LinearVolterra.Curve ℂ => (lam,a)) J q :=
    hasFDerivAt_prodMk_right lam q
  have hd := ((analyticOnNhd_classicalHillDiscriminant_joint (lam,q) (mem_univ _)).differentiableAt.hasFDerivAt).comp q hi
  change HasFDerivAt (fun a : NLS.LinearVolterra.Curve ℂ => classicalHillDiscriminant a lam)
    ((fderiv ℂ (fun t : ℂ × NLS.LinearVolterra.Curve ℂ => classicalHillDiscriminant t.2 t.1)
      (lam,q)).comp J) q at hd
  have he : (classicalHillContinuedRoot (lam,q))⁻¹ •
      fderiv ℂ (fun a : NLS.LinearVolterra.Curve ℂ => classicalHillDiscriminant a lam) q =
      ((classicalHillContinuedRoot (lam,q))⁻¹ •
        fderiv ℂ (fun t : ℂ × NLS.LinearVolterra.Curve ℂ => classicalHillDiscriminant t.2 t.1)
          (lam,q)).comp J := by
    rw [hd.fderiv]
    rfl
  rw [he]
  exact (hasFDerivAt_classicalHillContinuedPrimitive (lam,q) h).comp q hi

/-- One ball and one constant work for every contour, including the low
modes. These are estimates for the actual free-normalized continuation. -/
theorem exists_classicalHill_uniform_contour_primitive_bounds :
    ∃ R C : ℝ, 0 < R ∧ R ≤ 1 ∧ 0 < C ∧
      ∀ q : NLS.LinearVolterra.Curve ℂ, ‖q‖ < R → ∀ k : ℕ+,
        ∀ z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4),
          (z^2,q) ∈ classicalHillContinuationDomain ∧
          ‖fderiv ℂ (fun a : NLS.LinearVolterra.Curve ℂ =>
            classicalHillContinuedPrimitive (z^2,a)) q‖ ≤ C ∧
          ‖classicalHillContinuedPrimitive (z^2,q)-classicalHillFreePrimitive (z^2)‖ ≤ C*‖q‖ ∧
          ‖classicalHillContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi‖ ≤ Real.pi/4+C*‖q‖ := by
  obtain ⟨R,b,hR,hR1,hb,hroot⟩ := exists_classicalHill_uniform_contour_root_bound
  let C : ℝ := (4*Real.exp (Real.pi/4+3))/b
  have hC : 0 < C := by dsimp only [C]; positivity
  have hder (q : NLS.LinearVolterra.Curve ℂ) (hq : ‖q‖ < R) (k : ℕ+) (z : ℂ)
      (hz : z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)) :
      ‖fderiv ℂ (fun a : NLS.LinearVolterra.Curve ℂ =>
        classicalHillContinuedPrimitive (z^2,a)) q‖ ≤ C := by
    obtain ⟨hcover,hbound⟩ := hroot q hq k z hz
    rw [(hasFDerivAt_classicalHillContinuedPrimitive_source (z^2) q hcover).fderiv]
    apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
    rw [norm_inv]
    have hinv : ‖classicalHillContinuedRoot (z^2,q)‖⁻¹ ≤ b⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hb hbound
    have htrace := norm_fderiv_classicalHillDiscriminant_source_le (Real.pi/4) z
      (freeFrequencyCircle_im_le k z hz) q (hq.trans_le hR1)
    calc
      _ ≤ b⁻¹*(4*Real.exp (Real.pi/4+3)) :=
        mul_le_mul hinv htrace (ContinuousLinearMap.opNorm_nonneg _) (by positivity)
      _ = C := by dsimp only [C]; ring
  refine ⟨R,C,hR,hR1,hC,?_⟩
  intro q hq k z hz
  have hdiff : ‖classicalHillContinuedPrimitive (z^2,q)-classicalHillFreePrimitive (z^2)‖ ≤ C*‖q‖ := by
    have hd (a : NLS.LinearVolterra.Curve ℂ) (ha : a ∈ ball 0 R) :
        DifferentiableAt ℂ (fun p : NLS.LinearVolterra.Curve ℂ =>
          classicalHillContinuedPrimitive (z^2,p)) a := by
      exact (hasFDerivAt_classicalHillContinuedPrimitive_source (z^2) a
        (hroot a (by simpa only [mem_ball,dist_zero_right] using ha) k z hz).1).differentiableAt
    have he := (convex_ball (0 : NLS.LinearVolterra.Curve ℂ) R).norm_image_sub_le_of_norm_fderiv_le
      (𝕜 := ℂ) hd (fun a ha => hder a (by simpa only [mem_ball,dist_zero_right] using ha) k z hz)
      (mem_ball_self hR) (by simpa only [mem_ball,dist_zero_right] using hq)
    simpa only [classicalHillContinuedPrimitive_base,sub_zero] using he
  refine ⟨(hroot q hq k z hz).1,hder q hq k z hz,hdiff,?_⟩
  have hfree : classicalHillFreePrimitive (z^2)+I*(k : ℂ)*Real.pi =
      -I*(z-(Real.pi : ℂ)*(k : ℕ)) := by
    rw [classicalHillFreePrimitive,sqrt_sq_of_re_pos z
      (re_pos_of_high_closedBall _ k.property z (sphere_subset_closedBall hz))]
    ring
  have hnorm : ‖classicalHillFreePrimitive (z^2)+I*(k : ℂ)*Real.pi‖ = Real.pi/4 := by
    rw [hfree,norm_mul,norm_neg,norm_I,one_mul,mem_sphere_iff_norm.mp hz]
  calc
    _ = ‖(classicalHillContinuedPrimitive (z^2,q)-classicalHillFreePrimitive (z^2))+
        (classicalHillFreePrimitive (z^2)+I*(k : ℂ)*Real.pi)‖ := by congr 1; ring
    _ ≤ ‖classicalHillContinuedPrimitive (z^2,q)-classicalHillFreePrimitive (z^2)‖+
        ‖classicalHillFreePrimitive (z^2)+I*(k : ℂ)*Real.pi‖ := norm_add_le _ _
    _ ≤ C*‖q‖+Real.pi/4 := add_le_add hdiff hnorm.le
    _ = _ := by ring

end NLS.KdV
