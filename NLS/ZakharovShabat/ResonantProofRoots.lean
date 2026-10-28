import NLS.ComplexAnalysis.ZeroCountPowers
import NLS.ComplexAnalysis.SimpleAnalyticZero
import NLS.ZakharovShabat.ResonantDeterminantBounds

/-! # The literal Rouche and pointwise root arguments in Lemma 6.9

The proof first counts the diagonal residual, then its square, then the
actual quadratic determinant. All root factorizations are pointwise.
-/
noncomputable section
open NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

/-- The two strict boundary comparisons used in the source Rouche argument. -/
theorem resonantProof_boundary_comparisons (q a b c : ℂ) (hq : ‖q‖ = Real.pi / 4)
    (ha : ‖a‖ ≤ Real.pi / 32) (hb : ‖b‖ ≤ Real.pi / 16)
    (hc : ‖c‖ ≤ Real.pi / 16) :
    ‖(q-a)-q‖ < ‖q‖ ∧ ‖((q-a)^2-b*c)-(q-a)^2‖ < ‖(q-a)^2‖ := by
  constructor
  · simpa only [sub_sub_cancel_left, norm_neg, hq] using
      ha.trans_lt (by linarith [Real.pi_pos])
  · have hqa := norm_le_norm_sub_add q a
    have hgap : Real.pi / 16 < ‖q-a‖ := by rw [hq] at hqa; linarith [Real.pi_pos]
    have hprod : ‖b*c‖ ≤ (Real.pi / 16)^2 := by
      rw [norm_mul, pow_two]
      exact mul_le_mul hb hc (norm_nonneg _) (by positivity)
    simp only [sub_sub_cancel_left, norm_neg, norm_pow]
    exact hprod.trans_lt (by nlinarith [norm_nonneg (q-a), Real.pi_pos])

/-- The literal sequence of counts: one for h, two for h squared, then two for the determinant, with no exterior strip zeros. -/
theorem resonantProof_two_step_rouche (n : ℤ) (a b c : ℂ → ℂ)
    (ha : AnalyticOnNhd ℂ a (resonantStrip n))
    (hb : AnalyticOnNhd ℂ b (resonantStrip n))
    (hc : AnalyticOnNhd ℂ c (resonantStrip n))
    (hab : ∀ z ∈ resonantStrip n, ‖a z‖ ≤ Real.pi/32)
    (hbb : ∀ z ∈ resonantStrip n, ‖b z‖ ≤ Real.pi/16)
    (hcb : ∀ z ∈ resonantStrip n, ‖c z‖ ≤ Real.pi/16) :
    let h := fun z => z-(Real.pi : ℂ)*n-a z
    let d := fun z => (h z)^2-b z*c z
    analyticZeroCount h (refinedResonantDisk n) = 1 ∧
    analyticZeroCount (fun z => (h z)^2) (refinedResonantDisk n) = 2 ∧
    analyticZeroCount d (refinedResonantDisk n) = 2 ∧
    ∀ z ∈ resonantStrip n, z ∉ refinedResonantDisk n → d z ≠ 0 := by
  let center : ℂ := (Real.pi : ℂ)*n
  let h := fun z => z-center-a z
  let d := fun z => (h z)^2-b z*c z
  change analyticZeroCount h _ = 1 ∧ analyticZeroCount (fun z => (h z)^2) _ = 2 ∧
    analyticZeroCount d _ = 2 ∧ _
  have hr : 0 < Real.pi/4 := by positivity
  have hsub : Metric.closedBall center (Real.pi/4) ⊆ resonantStrip n :=
    closedBall_subset_resonantStrip n (by linarith [Real.pi_pos])
  have hh : AnalyticOnNhd ℂ h (resonantStrip n) := by
    intro z hz
    exact (analyticAt_id.sub analyticAt_const).sub (ha z hz)
  have hd : AnalyticOnNhd ℂ d (resonantStrip n) := by
    intro z hz
    exact ((hh z hz).pow 2).sub ((hb z hz).mul (hc z hz))
  have hbound (z : ℂ) (hz : z ∈ Metric.sphere center (Real.pi/4)) :
      ‖h z-(z-center)‖ < ‖z-center‖ ∧ ‖d z-(h z)^2‖ < ‖(h z)^2‖ := by
    have hs := hsub (Metric.sphere_subset_closedBall hz)
    exact resonantProof_boundary_comparisons _ _ _ _ (by simpa [dist_eq_norm] using hz)
      (hab z hs) (hbb z hs) (hcb z hs)
  have hnonzero (z : ℂ) (hz : z ∈ Metric.sphere center (Real.pi/4)) : h z ≠ 0 :=
    (rouche_ratio_mem_slitPlane (hbound z hz).1).2.1
  have dnonzero (z : ℂ) (hz : z ∈ Metric.sphere center (Real.pi/4)) : d z ≠ 0 :=
    (rouche_ratio_mem_slitPlane (hbound z hz).2).2.1
  have hcount : analyticZeroCount h (Metric.closedBall center (Real.pi/4)) = 1 :=
    analyticZeroCount_eq_degree_of_boundary_lt 1 hr (hh.mono hsub)
      (by simpa only [pow_one] using fun z hz => (hbound z hz).1)
  have hcount_open : analyticZeroCount h (refinedResonantDisk n) = 1 := by
    rw [refinedResonantDisk, analyticZeroCount_ball_eq_closedBall hnonzero, hcount]
  refine ⟨hcount_open, ?_, ?_, ?_⟩
  · rw [analyticZeroCount_pow h _ (hh.mono (refinedResonantDisk_subset_strip n)), hcount_open]
  · rw [refinedResonantDisk, analyticZeroCount_ball_eq_closedBall dnonzero,
      analyticZeroCount_eq_of_boundary_lt hr ((hh.mono hsub).pow 2) (hd.mono hsub)
        (fun z hz => (hbound z hz).2)]
    change analyticZeroCount (fun z => (h z)^2) _ = 2
    rw [analyticZeroCount_pow h _ (hh.mono hsub), hcount]

  · intro z hz hout hzero
    have hn := norm_resonant_quadratic_root_le (z-center) (a z) (b z) (c z)
      (hab z hz) (hbb z hz) (hcb z hz) hzero
    apply hout
    change dist z center < Real.pi/4
    rw [dist_eq_norm]
    exact hn.trans_lt (by linarith [Real.pi_pos])

/-- Pointwise factorization for any square root of the off-diagonal product; no analytic branch is assumed. -/
theorem resonantProof_root_factorization (q a b c s : ℂ) (hs : s^2 = b*c) :
    (q-a)^2-b*c = (q-a-s)*(q-a+s) := by
  rw [← hs]
  ring

/-- Either sign of a pointwise square root describes the actual quadratic zero. -/
theorem resonantProof_root_alternatives (q a b c s : ℂ) (hs : s^2 = b*c) :
    (q-a)^2-b*c = 0 ↔ q = a+s ∨ q = a-s := by
  rw [resonantProof_root_factorization q a b c s hs, mul_eq_zero]
  constructor
  · rintro (he | he)
    · left
      linear_combination he
    · right
      linear_combination he
  · rintro (rfl | rfl) <;> simp

/-- The residual modulus is the real square root of the product norm and bounds the displacement. -/
theorem resonantProof_root_modulus (q a b c : ℂ) (hz : (q-a)^2-b*c = 0) :
    ‖q-a‖ = Real.sqrt ‖b*c‖ ∧ ‖q‖ ≤ ‖a‖ + Real.sqrt ‖b*c‖ := by
  have he : ‖q-a‖^2 = ‖b*c‖ := by
    simpa only [norm_pow] using congrArg norm (sub_eq_zero.mp hz)
  have hr : ‖q-a‖ = Real.sqrt ‖b*c‖ := by
    rw [← he, Real.sqrt_sq (norm_nonneg _)]
  exact ⟨hr, by simpa only [hr, add_comm] using norm_le_norm_sub_add q a⟩

/-- The literal Rouche count gives a unique simple diagonal zero on the whole strip. -/
theorem resonantProof_unique_simple_diagonal (n : ℤ) (a : ℂ → ℂ)
    (ha : AnalyticOnNhd ℂ a (resonantStrip n))
    (hab : ∀ z ∈ resonantStrip n, ‖a z‖ ≤ Real.pi/32) :
    let h := fun z => z-(Real.pi : ℂ)*n-a z
    ∃ x ∈ refinedResonantDisk n, h x = 0 ∧ analyticOrderAt h x = 1 ∧
      ∀ z ∈ resonantStrip n, h z = 0 ↔ z = x := by
  let center : ℂ := (Real.pi : ℂ)*n
  let h := fun z => z-center-a z
  have hr : 0 < Real.pi/4 := by positivity
  have hsub : Metric.closedBall center (Real.pi/4) ⊆ resonantStrip n :=
    closedBall_subset_resonantStrip n (by linarith [Real.pi_pos])
  have hh : AnalyticOnNhd ℂ h (resonantStrip n) := by
    intro z hz
    exact (analyticAt_id.sub analyticAt_const).sub (ha z hz)
  have hbound (z : ℂ) (hz : z ∈ Metric.sphere center (Real.pi/4)) :
      ‖h z-(z-center)‖ < ‖z-center‖ :=
    (resonantProof_boundary_comparisons (z-center) (a z) 0 0
      (by simpa [dist_eq_norm] using hz) (hab z (hsub (Metric.sphere_subset_closedBall hz)))
      (by simp; positivity) (by simp; positivity)).1
  have hnonzero (z : ℂ) (hz : z ∈ Metric.sphere center (Real.pi/4)) : h z ≠ 0 :=
    (rouche_ratio_mem_slitPlane (hbound z hz)).2.1
  have hcount : analyticZeroCount h (Metric.closedBall center (Real.pi/4)) = 1 :=
    analyticZeroCount_eq_degree_of_boundary_lt 1 hr (hh.mono hsub)
      (by simpa only [pow_one] using hbound)
  obtain ⟨b,hb⟩ := NormedSpace.sphere_nonempty (E := ℂ) (x := center) |>.mpr hr.le
  have hbclosed := Metric.sphere_subset_closedBall hb
  obtain ⟨x,hx,hx0,horder,hunique⟩ := exists_unique_simple_analytic_zero (hh.mono hsub)
    (fun z hz => analyticOrderAt_ne_top_on_connected
      (Metric.isConnected_closedBall hr.le).isPreconnected (hh.mono hsub)
      hbclosed (hnonzero b hb) hz)
    (finite_analytic_zeros (isCompact_closedBall _ _) (Metric.isConnected_closedBall hr.le)
      (hh.mono hsub) hbclosed (hnonzero b hb)) hcount
  have hxopen : x ∈ refinedResonantDisk n :=
    lt_of_le_of_ne hx (fun he => hnonzero x he hx0)
  refine ⟨x,hxopen,hx0,horder,?_⟩
  intro z hz
  constructor
  · intro hz0
    have hzbound : ‖z-center‖ ≤ Real.pi/32 := by
      have he : z-center = a z := sub_eq_zero.mp hz0
      rw [he]
      exact hab z hz
    exact (hunique z (by
      apply Metric.mem_closedBall.mpr
      rw [dist_eq_norm]
      exact hzbound.trans (by linarith [Real.pi_pos]))).mp hz0
  · rintro rfl
    exact hx0

end NLS.ZakharovShabat
