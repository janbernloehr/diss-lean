import NLS.ComplexAnalysis.UniformAnalyticBallVariation

/-! # A common positive-real-part ball for a uniformly bounded analytic family -/
noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*}

theorem exists_uniform_ball_positive_re (f : ι → E → ℂ) (R M : ℝ) (a : ℂ)
    (hR : 0 < R) (hM : 0 < M) (ha : 0 < a.re)
    (hf : ∀ i, AnalyticOnNhd ℂ (f i) (ball (0 : E) R))
    (hb : ∀ i, ∀ x ∈ ball (0 : E) R, ‖f i x‖ ≤ M) (hzero : ∀ i, f i 0 = a) :
    ∃ η : ℝ, 0 < η ∧ η ≤ R ∧ ∀ i, ∀ x ∈ ball (0 : E) η,
      ‖f i x-a‖ ≤ a.re/2 ∧ 0 < (f i x).re := by
  let η := min (R/2) (a.re*R/(16*M))
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hηR : η ≤ R := (min_le_left _ _).trans (by linarith)
  refine ⟨η,hη,hηR,?_⟩
  intro i x hx
  have hxhalf : x ∈ ball (0 : E) (R/2) := ball_subset_ball (min_le_left _ _) hx
  have hvar := norm_sub_base_le_of_analytic_ball_bound (f i) 0 hR (hf i) (hb i) hxhalf
  rw [hzero i,sub_zero] at hvar
  have hsmall : ‖x‖ ≤ a.re*R/(16*M) := (mem_ball_zero_iff.mp hx).le.trans (min_le_right _ _)
  have hbudget : (4*M/R)*‖x‖ ≤ a.re/4 := by
    apply (mul_le_mul_of_nonneg_left hsmall (by positivity : 0 ≤ 4*M/R)).trans_eq
    field_simp
    ring
  have hre := re_le_norm (a-f i x)
  rw [sub_re,norm_sub_rev] at hre
  constructor <;> linarith

end NLS.ComplexAnalysis
