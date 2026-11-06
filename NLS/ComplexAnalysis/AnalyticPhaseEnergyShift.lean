import NLS.ComplexAnalysis.NormalizedSquareRootBounds

/-! # Analytic phases under a constant translation of squared frequency -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.ComplexAnalysis

/-- Translating energy preserves the normalized analytic phase at infinity.
The new frequency and the phase correction are constructed by the square
root equal to one at the inversion origin. -/
theorem exists_analytic_phase_energy_shift
    (c : ℂ) (A : ℂ → ℂ) (hA : AnalyticAt ℂ A 0) (hA0 : A 0 = 0)
    (R : ℝ) :
    ∃ T : ℝ, 0 < T ∧ ∃ B : ℂ → ℂ, AnalyticAt ℂ B 0 ∧ B 0 = 0 ∧
      ∀ z : ℂ, T < ‖z‖ → ∃ ζ : ℂ, R < ‖ζ‖ ∧ ζ^2 = z^2+c ∧
        -I*z+B z⁻¹ = -I*ζ+A ζ⁻¹ := by
  let H : ℂ → ℂ := fun w => Complex.sqrt (1+c*w^2)
  have hH0 : H 0 = 1 := by simp [H]
  have hH : AnalyticAt ℂ H 0 := by
    have hs : AnalyticAt ℂ Complex.sqrt 1 :=
      Complex.differentiableOn_sqrt.analyticAt
        (Complex.isOpen_slitPlane.mem_nhds (by simp [mem_slitPlane_iff]))
    exact hs.comp_of_eq (f := fun w : ℂ => 1+c*w^2)
      (analyticAt_const.add (analyticAt_const.mul (analyticAt_id.pow 2))) (by simp)
  have hsq (w : ℂ) : H w^2 = 1+c*w^2 := by
    have hh := Complex.cpow_nat_inv_pow (1+c*w^2) (Nat.succ_ne_zero 1)
    norm_num at hh
    simpa only [H,Complex.sqrt,one_div] using hh
  let B : ℂ → ℂ := fun w => -I*c*w/(H w+1)+A (w/H w)
  have hB : AnalyticAt ℂ B 0 := by
    have hquot : AnalyticAt ℂ (fun w : ℂ => w/H w) 0 :=
      analyticAt_id.div hH (by rw [hH0]; norm_num)
    have hcomp : AnalyticAt ℂ (fun w : ℂ => A (w/H w)) 0 := by
      exact hA.comp_of_eq (f := fun w : ℂ => w/H w) hquot (by simp)
    exact ((analyticAt_const.mul analyticAt_id).div
      (hH.add analyticAt_const) (by change H 0+1 ≠ 0; rw [hH0]; norm_num)).add hcomp
  have hB0 : B 0 = 0 := by simp [B,hA0]
  have hnear : ∀ᶠ w : ℂ in nhds 0, ‖H w-1‖ < (1/2 : ℝ) := by
    have hn : ContinuousAt (fun w : ℂ => ‖H w-1‖) 0 :=
      (hH.continuousAt.sub continuousAt_const).norm
    exact hn.eventually (gt_mem_nhds (by simp [hH0]))
  obtain ⟨δ,hδ,hδbound⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨max 1 (max δ⁻¹ (2*R)),lt_of_lt_of_le zero_lt_one (le_max_left _ _),B,hB,hB0,?_⟩
  intro z hz
  have hz0 : 0 < ‖z‖ := lt_trans zero_lt_one ((le_max_left _ _).trans_lt hz)
  have hzn : z ≠ 0 := norm_pos_iff.mp hz0
  have hw : ‖z⁻¹‖ < δ := by
    rw [norm_inv]
    have hh := (le_trans (le_max_left δ⁻¹ (2*R)) (le_max_right 1 _)).trans_lt hz
    exact (inv_lt_comm₀ hz0 hδ).mpr hh
  have hclose : ‖H z⁻¹-1‖ < (1/2 : ℝ) := hδbound (by simpa [dist_zero_right] using hw)
  have hlow : (1/2 : ℝ) < ‖H z⁻¹‖ := by
    have hh := norm_sub_norm_le (1 : ℂ) (H z⁻¹)
    rw [norm_one,norm_sub_rev] at hh
    linarith
  have hHn : H z⁻¹ ≠ 0 := norm_pos_iff.mp (by linarith)
  have hHp : H z⁻¹+1 ≠ 0 := by
    intro he
    have hh : H z⁻¹ = -1 := eq_neg_of_add_eq_zero_left he
    norm_num [hh] at hclose
  refine ⟨z*H z⁻¹,?_,?_,?_⟩
  · rw [norm_mul]
    have hr := (le_trans (le_max_right δ⁻¹ (2*R)) (le_max_right 1 _)).trans_lt hz
    nlinarith
  · calc
      (z*H z⁻¹)^2 = z^2*(1+c*(z⁻¹)^2) := by rw [mul_pow,hsq]
      _ = z^2+c := by field_simp
  · have hinv : (z*H z⁻¹)⁻¹ = z⁻¹/H z⁻¹ := by simp [div_eq_mul_inv,mul_inv_rev,mul_comm]
    rw [hinv]
    dsimp only [B]
    rw [←add_assoc]
    congr 1
    have hs := hsq z⁻¹
    field_simp [hzn,hHp]
    field_simp at hs
    linear_combination hs

end NLS.ComplexAnalysis
