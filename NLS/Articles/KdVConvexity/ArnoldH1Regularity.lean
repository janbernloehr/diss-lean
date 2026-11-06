import NLS.Articles.KdVConvexity.GlobalArnoldCalibration
import NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianRegularity
import NLS.SequenceSpaces.PositiveSupportedMembership

/-! # The original cubic-weighted Arnold action condition implies physical H1 regularity -/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.Articles.KdVConvexity
open NLS.KdV NLS.Articles.KdVKdV2Frequencies

theorem intrinsic_Arnold_positive_calibration
    (D : GlobalRoughAbelianForwardData) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    hillHminusRealGapContourMoment q hr n 0 =
      (((1+(n : ℝ))*‖D.positive q (n : ℤ)‖^2 : ℝ) : ℂ) := by
  obtain ⟨Ω,I,_hΩ,hreal,hI,hrec,_hpos,_hzero,_hI0,_hinv⟩ :=
    exists_global_analytic_weighted_Arnold_action_map
  exact (hrec q hr n).symm.trans (global_Arnold_positive_calibration D Ω hreal I hI hrec q hr n)

theorem source_H1_of_cubic_weighted_Arnold_summable
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (hs : Summable (fun n : ℕ+ => (n : ℝ)^3*‖hillHminusRealGapContourMoment q hr n 0‖)) :
    Memℓp (fun k => (Weight.sobolev 1 k : ℂ)*q.val k) 2 := by
  obtain ⟨D⟩ := nonempty_globalRoughAbelianForwardData
  have hcal (n : ℕ+) : ‖hillHminusRealGapContourMoment q hr n 0‖ =
      (1+(n : ℝ))*‖D.positive q (n : ℤ)‖^2 := by
    rw [intrinsic_Arnold_positive_calibration D q hr n,norm_real,Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  let f : ℤ → ℂ := fun k => (Weight.sobolev 2 k : ℂ)*D.positive q k
  have hbound (n : ℕ+) : ‖f (n : ℤ)‖^2 ≤
      8*((n : ℝ)^3*‖hillHminusRealGapContourMoment q hr n 0‖) := by
    have hn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast n.pos
    have hc : (1+(n : ℝ))^3 ≤ 8*(n : ℝ)^3 := by
      calc
        _ ≤ (2*(n : ℝ))^3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
        _ = _ := by ring
    have he : ‖f (n : ℤ)‖^2 = (1+(n : ℝ))^3*((1+(n : ℝ))*‖D.positive q (n : ℤ)‖^2) := by
      dsimp only [f]
      rw [norm_mul,norm_real,Real.norm_eq_abs,abs_of_pos (Weight.positive _ _)]
      simp only [Weight.sobolev_apply,Int.cast_natCast,Nat.abs_cast,Real.rpow_two]
      ring
    rw [he,hcal]
    nlinarith [mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ (1+(n : ℝ))*‖D.positive q (n : ℤ)‖^2)]
  have hfp : Summable (fun n : ℕ+ => ‖f (n : ℤ)‖^2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hbound (hs.mul_left 8)
  have hf : Memℓp f 2 := memlp_two_of_positive_support f (fun k hk => by
    simp only [f,D.positive_zero q (D.real_mem_domain q hr) k hk,mul_zero]) hfp
  exact (D.sobolev_iff_positive_mem q hr 1 (by norm_num)).mpr (by simpa only [one_add_one_eq_two] using hf)

end NLS.Articles.KdVConvexity
