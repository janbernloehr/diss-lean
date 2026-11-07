import NLS.Articles.KdVEstimates.MainBirkhoffEstimates
import NLS.KdV.HillOriginalBirkhoffRealSobolevRestriction
import NLS.KdV.HillRealSobolevSourceNorm

noncomputable section
set_option autoImplicit false
open NLS.KdV
namespace NLS.Articles.KdVEstimates

/-- Corollary 1, second occurrence, part (i), for every real s>=0. -/
theorem corollary1_real_sobolev_norm (s : ℝ) (hs : 0 ≤ s) :
    ∃ c : ℝ, 0 < c ∧
      ∀ p : RealHillWeightedPotential (SpectralWeight.piSobolev s hs),
      ∀ hmean : p.val.val 0 = 0,
      ‖hillOriginalBirkhoffRealSobolevRestriction s hs p hmean‖ ≤
        c*(1+‖p.val‖)^(max 1 s)*‖p.val‖ := by
  let r := SpectralWeight.corollarySplit s
  have hr := SpectralWeight.corollarySplit_bounds s hs
  let v := SpectralWeight.piSobolev (s-r) (sub_nonneg.mpr hr.2.2)
  obtain ⟨c,hc,hbound⟩ := theorem3_birkhoff r hr.1 hr.2.1 v
  let D := (Real.pi^r)*(c*(1+(17*(1+Real.pi))^s))
  refine ⟨D,by dsimp only [D]; positivity,?_⟩
  intro p hmean
  let q := hillRealWeightedInclusion _ _ (SpectralWeight.corollaryWeight_le s hs) p
  have hqmean : q.val.val 0 = 0 := by simpa only [q,hillRealWeightedInclusion_apply] using hmean
  have hqp : ‖q.val‖ ≤ ‖p.val‖ := norm_hillRealWeightedInclusion_le _ _ _ p
  have h1 := norm_hillCorollaryTarget_le s hs
    (hillOriginalBirkhoffWeightedRestriction (SpectralWeight.corollaryWeight s hs) q hqmean)
  have h2 := hbound q hqmean
  change ‖hillOriginalBirkhoffWeightedRestriction (SpectralWeight.corollaryWeight s hs) q hqmean‖ ≤
    c*((1+‖q.val‖)+(SpectralWeight.corollaryWeight s hs).realExtension
      (16*‖q.val‖^(3/2-SpectralWeight.corollarySplit s)))*‖q.val‖ at h2
  have h3 := SpectralWeight.corollaryWeight_polynomial_bound s hs ‖q.val‖ (norm_nonneg _)
  have hpow : (1+‖q.val‖)^(max 1 s) ≤ (1+‖p.val‖)^(max 1 s) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
  have hprod := mul_le_mul hpow hqp (norm_nonneg _) (by positivity)
  change ‖hillOriginalBirkhoffRealSobolevRestriction s hs p hmean‖ ≤ _ at h1
  have hB := mul_le_mul_of_nonneg_right h3 (norm_nonneg q.val)
  have hC := mul_le_mul_of_nonneg_left hB hc.le
  have h4 := h2.trans (by simpa only [mul_assoc] using hC)
  have h5 := mul_le_mul_of_nonneg_left h4 (Real.rpow_nonneg Real.pi_pos.le r)
  have h6 := mul_le_mul_of_nonneg_left hprod (show 0 ≤ D by dsimp only [D]; positivity)
  exact (h1.trans h5).trans (by simpa only [D,mul_assoc] using h6)

theorem hasSum_original_real_sobolev_actions (s : ℝ) (hs : 0 ≤ s)
    (p : RealHillWeightedPotential (SpectralWeight.piSobolev s hs)) (hmean : p.val.val 0 = 0) :
    HasSum (fun k : ℕ => (2*Real.pi*(k+1 : ℕ))^(2*s+1)*
      hillOriginalBirkhoffAction
        (hillOriginalWeightedMeanZeroSource (SpectralWeight.piSobolev s hs) p hmean) k)
      (‖hillOriginalBirkhoffRealSobolevRestriction s hs p hmean‖^2/2) := by
  let z := hillOriginalBirkhoffRealSobolevRestriction s hs p hmean
  have h := (summable_HillBirkhoffRealSobolevSpace_sq s z).hasSum
  rw [← norm_HillBirkhoffRealSobolevSpace_sq s z] at h
  have hh := h.div_const 2
  apply hh.congr
  intro K
  apply Finset.sum_congr rfl
  intro k _
  dsimp only [z]
  rw [hillOriginalBirkhoffAction,← hillOriginalBirkhoffRealSobolevRestriction_coordinates s hs p hmean k]
  ring

/-- BOTH parts of the real-exponent Corollary 1 with one constant, the exact
homogeneous target, the original physical map and a genuinely convergent action sum. -/
theorem corollary1_real_sobolev (s : ℝ) (hs : 0 ≤ s) :
    ∃ c : ℝ, 0 < c ∧
      ∀ p : RealHillWeightedPotential (SpectralWeight.piSobolev s hs),
      ∀ hmean : p.val.val 0 = 0,
      (‖hillOriginalBirkhoffRealSobolevRestriction s hs p hmean‖ ≤
        c*(1+‖p.val‖)^(max 1 s)*‖p.val‖) ∧
      Summable (fun k : ℕ => (2*Real.pi*(k+1 : ℕ))^(2*s+1)*
        hillOriginalBirkhoffAction
          (hillOriginalWeightedMeanZeroSource (SpectralWeight.piSobolev s hs) p hmean) k) ∧
      (∑' k : ℕ, (2*Real.pi*(k+1 : ℕ))^(2*s+1)*
        hillOriginalBirkhoffAction
          (hillOriginalWeightedMeanZeroSource (SpectralWeight.piSobolev s hs) p hmean) k) ≤
        c^2*(1+‖p.val‖)^(2*max 1 s)*‖p.val‖^2 := by
  obtain ⟨c,hc,hbound⟩ := corollary1_real_sobolev_norm s hs
  refine ⟨c,hc,?_⟩
  intro p hmean
  have hsum := hasSum_original_real_sobolev_actions s hs p hmean
  refine ⟨hbound p hmean,hsum.summable,?_⟩
  rw [hsum.tsum_eq]
  have hh := pow_le_pow_left₀ (norm_nonneg _) (hbound p hmean) 2
  have he : ((1+‖p.val‖)^(max 1 s))^2 = (1+‖p.val‖)^(2*max 1 s) := by
    rw [← Real.rpow_mul_natCast (by positivity)]; congr 1; norm_num; ring
  rw [mul_pow,mul_pow,he] at hh
  nlinarith [sq_nonneg ‖hillOriginalBirkhoffRealSobolevRestriction s hs p hmean‖]

end NLS.Articles.KdVEstimates
