import NLS.KdV.HillEnergyNumeratorPeriods

/-! Entire energy numerators with the same vanishing retained periods
and sub-sine differential growth are scalar multiples. The scalar is
fixed by the actual omitted period, with no universal normalization. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

theorem hillEnergyNumerator_eq_scalar_of_retained_periods
    (u : PeriodOneRealL2) (c : ℂ) (n : ℕ+)
    (D : ∀ m : ℕ+, SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) ((m:ℕ):ℤ))
    (F G : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F univ) (hG : AnalyticOnNhd ℂ G univ)
    (hFp : ∀ m : ℕ+, m ≠ n → hillEnergyNumeratorPeriod c (hillMiuraDiagonal u.val) (D m) F = 0)
    (hGp : ∀ m : ℕ+, m ≠ n → hillEnergyNumeratorPeriod c (hillMiuraDiagonal u.val) (D m) G = 0)
    (hGn : hillEnergyNumeratorPeriod c (hillMiuraDiagonal u.val) (D n) G ≠ 0)
    (hFs : ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∀ z ∈ sphere (0:ℂ) (centralCircleRadius k), ‖(2*z*F (z^2-c))/(-2*sin z)‖ ≤ ε)
    (hGs : ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∀ z ∈ sphere (0:ℂ) (centralCircleRadius k), ‖(2*z*G (z^2-c))/(-2*sin z)‖ ≤ ε) :
    ∃ A : ℂ, F = fun E => A*G E := by
  let A := hillEnergyNumeratorPeriod c (hillMiuraDiagonal u.val) (D n) F/
    hillEnergyNumeratorPeriod c (hillMiuraDiagonal u.val) (D n) G
  let P : ℂ → ℂ := fun E => F E-A*G E
  have hAG : AnalyticOnNhd ℂ (fun E => A*G E) univ := analyticOnNhd_const.mul hG
  have hP : AnalyticOnNhd ℂ P univ := hF.sub hAG
  have hzero : P = 0 := by
    apply hillEnergyNumerator_eq_zero_of_positive_periods u c P hP
    · intro m
      refine ⟨D m,?_⟩
      rw [hillEnergyNumeratorPeriod_sub c _ (D m) F (fun E => A*G E) hF hAG,
        hillEnergyNumeratorPeriod_const_mul]
      by_cases hmn : m = n
      · subst m
        dsimp only [A]
        rw [div_mul_cancel₀ _ hGn,sub_self]
      · rw [hFp m hmn,hGp m hmn,mul_zero,sub_self]
    · intro ε hε
      obtain ⟨KF,hKF⟩ := hFs (ε/2) (half_pos hε)
      obtain ⟨KG,hKG⟩ := hGs (ε/(2*(‖A‖+1))) (by positivity)
      refine ⟨max KF KG,?_⟩
      intro k hk z hz
      have hf := hKF k ((le_max_left _ _).trans hk) z hz
      have hg := hKG k ((le_max_right _ _).trans hk) z hz
      have he : (2*z*P (z^2-c))/(-2*sin z) =
          (2*z*F (z^2-c))/(-2*sin z)-A*((2*z*G (z^2-c))/(-2*sin z)) := by dsimp only [P]; ring
      rw [he]
      have hb : ‖A‖*(ε/(2*(‖A‖+1))) ≤ ε/2 := by
        calc
          _ = (‖A‖/(‖A‖+1))*(ε/2) := by field_simp
          _ ≤ 1*(ε/2) := mul_le_mul_of_nonneg_right
            ((div_le_iff₀ (by positivity : 0 < ‖A‖+1)).mpr (by linarith)) (half_pos hε).le
          _ = _ := one_mul _
      calc
        _ ≤ ‖(2*z*F (z^2-c))/(-2*sin z)‖+‖A‖*‖(2*z*G (z^2-c))/(-2*sin z)‖ := by
          simpa only [norm_mul] using norm_sub_le ((2*z*F (z^2-c))/(-2*sin z)) (A*((2*z*G (z^2-c))/(-2*sin z)))
        _ ≤ ε/2+‖A‖*(ε/(2*(‖A‖+1))) := add_le_add hf (mul_le_mul_of_nonneg_left hg (norm_nonneg _))
        _ ≤ ε := by linarith
  refine ⟨A,?_⟩
  funext E
  have he := congrFun hzero E
  exact sub_eq_zero.mp he

end NLS.KdV
