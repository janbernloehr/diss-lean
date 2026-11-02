import NLS.KdV.ClassicalDiscriminantUniformVariation
import NLS.KdV.FreeContourUniformLowerBound
import NLS.KdV.ClassicalSourcePrimitive

/-! # One quantitative root bound for every positive frequency contour

A small norm ball of continuous complex potentials supports all the
positive fixed circles, with a common lower bound on the actual continued
root. The entire straight source segment is proved admissible.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem freeFrequencyCircle_im_le (k : ℕ+) (z : ℂ)
    (hz : z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)) : |z.im| ≤ Real.pi/4 := by
  have h := abs_im_le_norm (z-(Real.pi : ℂ)*(k : ℕ))
  rw [mem_sphere_iff_norm.mp hz] at h
  simpa only [sub_im,mul_im,ofReal_im,natCast_im,mul_zero,zero_mul,add_zero,sub_zero] using h

/-- The ball and positive lower bound are chosen before every contour
index and every potential in the ball. No cutoff or avoidance input is needed. -/
theorem exists_classicalHill_uniform_contour_root_bound :
    ∃ R b : ℝ, 0 < R ∧ R ≤ 1 ∧ 0 < b ∧
      ∀ q : NLS.LinearVolterra.Curve ℂ, ‖q‖ < R → ∀ k : ℕ+,
        ∀ z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4),
          (z^2,q) ∈ classicalHillContinuationDomain ∧
            b ≤ ‖classicalHillContinuedRoot (z^2,q)‖ := by
  obtain ⟨a,ha,hfree⟩ := exists_uniform_freeContour_radicand_lower_bound
  let L : ℝ := 16*(Real.exp (Real.pi/4+3))^2
  have hL : 0 < L := by dsimp only [L]; positivity
  let R : ℝ := min 1 (a/(2*L))
  have hR : 0 < R := lt_min (by norm_num) (by positivity)
  have hR1 : R ≤ 1 := min_le_left _ _
  have hrad (q : NLS.LinearVolterra.Curve ℂ) (hq : ‖q‖ < R) (k : ℕ+) (z : ℂ)
      (hz : z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)) :
      a/2 ≤ ‖classicalHillRadicand (z^2,q)‖ := by
    have hq1 := hq.trans_le hR1
    have hdiff := norm_classicalHillRadicand_sub_free_le (Real.pi/4) z
      (freeFrequencyCircle_im_le k z hz) q hq1
    have hqL := (lt_div_iff₀ (by positivity : 0 < 2*L)).mp
      (hq.trans_le (min_le_right 1 (a/(2*L))))
    have ht := norm_sub_norm_le (classicalHillRadicand (z^2,0)) (classicalHillRadicand (z^2,q))
    rw [norm_sub_rev] at ht
    change ‖classicalHillRadicand (z^2,q)-classicalHillRadicand (z^2,0)‖ ≤ L*‖q‖ at hdiff
    have hf := hfree k z hz
    nlinarith
  have hcover (q : NLS.LinearVolterra.Curve ℂ) (hq : ‖q‖ < R) (k : ℕ+) (z : ℂ)
      (hz : z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)) :
      (z^2,q) ∈ classicalHillContinuationDomain := by
    intro s hs
    have hsq : ‖(s : ℂ) • q‖ < R := by
      rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hs.1]
      exact (mul_le_mul_of_nonneg_right hs.2 (norm_nonneg q)).trans_lt (by simpa using hq)
    have hnonzero : classicalHillRadicand (z^2,(s : ℂ) • q) ≠ 0 :=
      norm_pos_iff.mp ((by positivity : (0 : ℝ) < a/2).trans_le (hrad _ hsq k z hz))
    simpa only [sourceSegmentMap,zero_add,sub_zero] using
      (show (z^2,(s : ℂ) • q) ∈ classicalHillRootDomain from
        ⟨sq_mem_slitPlane_of_high_circle _ k.property z hz,hnonzero⟩)
  refine ⟨R,Real.sqrt (a/2),hR,hR1,Real.sqrt_pos.mpr (by positivity),?_⟩
  intro q hq k z hz
  have hcont := hcover q hq k z hz
  refine ⟨hcont,?_⟩
  have he := congrArg norm (classicalHillContinuedRoot_sq (z^2,q) hcont)
  rw [norm_pow] at he
  have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ a/2)
  have hr := hrad q hq k z hz
  nlinarith [norm_nonneg (classicalHillContinuedRoot (z^2,q)),Real.sqrt_nonneg (a/2)]

end NLS.KdV
