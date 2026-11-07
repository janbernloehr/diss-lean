import NLS.KdV.HillHminusOneLowNormalizedActions
import NLS.ZakharovShabat.SourceHigherActionOneNormalizedReal

/-! The actual local Miura normalized action ratio is REAL POSITIVE
at every real native source, including an original closed gap. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillHminusMiuraGapBall

theorem diracSum_im_eq_zero_of_real (B : HillHminusMiuraGapBall) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) (hr : IsRealPeriodOneHminusOne q) :
    (B.diracSum n q).im = 0 := by
  let u : PeriodOneRealL2 := ⟨B.actionBall.lift q,B.actionBall.lift_real q hq hr⟩
  have he := canonicalPeriodicEndpoints_im_eq_zero_of_realType (by simp) (by norm_num)
    (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _)
    (isRealType_periodOnePotential _ (hillMiuraRealSource u).property) ((n:ℕ):ℤ)
  unfold diracSum sourceStandardRootMidpoint canonicalPeriodicMidpoint
  change (2*((canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential (hillMiuraDiagonal u.val))
    (periodOnePotential_mem _) ((n:ℕ):ℤ)+canonicalPeriodicRight (by simp) (by norm_num)
      (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _) ((n:ℕ):ℤ))/2)).im = 0
  simp only [Complex.mul_im,Complex.div_im,Complex.add_im,he.1,he.2,zero_add,zero_mul]
  norm_num

theorem normalizedRatio_real_positive (B : HillHminusMiuraGapBall) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) (hr : IsRealPeriodOneHminusOne q) :
    (B.normalizedRatio n q).im = 0 ∧ 0 < (B.normalizedRatio n q).re := by
  let u : PeriodOneRealL2 := ⟨B.actionBall.lift q,B.actionBall.lift_real q hq hr⟩
  let F := sourceHigherActionOneNormalized (by simp) (by norm_num) ((n:ℕ):ℤ) (hillMiuraDiagonal u.val)
  let S := B.diracSum n q
  have hFi : F.im = 0 := sourceHigherActionOneNormalized_im_eq_zero_of_realType (by simp) (by norm_num)
    (hillMiuraDiagonal u.val) (hillMiuraRealSource u).property ((n:ℕ):ℤ)
  have hFp : 0 < F.re := sourceHigherActionOneNormalized_re_pos_of_left_pos (by simp) (by norm_num)
    (hillMiuraRealSource u) ((n:ℕ):ℤ) (hillMiura_positive_gap_left_pos u (n:ℕ) (by exact_mod_cast n.pos))
  have hSi : S.im = 0 := B.diracSum_im_eq_zero_of_real n q hq hr
  have hSp : 0 < S.re := B.diracSum_re_pos_of_real n q hq hr
  have hF : (F.re:ℂ) = F := by simpa [hFi] using Complex.re_add_im F
  have hS : (S.re:ℂ) = S := by simpa [hSi] using Complex.re_add_im S
  have he : B.normalizedRatio n q = ((16*(Real.pi*(n:ℕ))*F.re/S.re^2:ℝ):ℂ) := by
    change (16*((Real.pi:ℂ)*(n:ℕ)))*F/S^2 = _
    rw [← hF,← hS]
    push_cast
    rfl
  rw [he]
  refine ⟨Complex.ofReal_im _,?_⟩
  rw [Complex.ofReal_re]
  have hn : 0 < ((n:ℕ):ℝ) := by exact_mod_cast n.pos
  exact div_pos (mul_pos (mul_pos (by norm_num) (mul_pos Real.pi_pos hn)) hFp) (sq_pos_of_pos hSp)

end NLS.KdV.HillHminusMiuraGapBall
