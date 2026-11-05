import NLS.KdV.HillCentralCounting

/-! # Central/tail separation from affine free-energy localization

These estimates use only the free energy lattice. They apply to any
actual characteristic whose roots have a bounded central part and an
arbitrarily thin affine tail, without an L2 operator bound.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.KdV

theorem freeHillValue_add_margin_lt_centralSeparator
    (N : ℕ) (hN : 2 ≤ N) (k : ℕ) (hk : k < N) :
    freeHillValue k+(N : ℝ)/4 < hillCentralSeparator N := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hkR : (k : ℝ) ≤ N := by exact_mod_cast hk.le
  have hsq : (k : ℝ)^2 ≤ (N : ℝ)^2 := (sq_le_sq₀ (by positivity) (by positivity)).mpr hkR
  have hgap := two_mul_nat_sub_one_le_abs_sq_sub_sq (n := N) (k := (k : ℤ))
    (by omega) (by simpa using ne_of_lt hk)
  simp only [Int.cast_natCast,abs_of_nonneg (sub_nonneg.mpr hsq)] at hgap
  have hpi : 9 < Real.pi^2 := by nlinarith [Real.pi_gt_three]
  have hp := mul_pos (sub_pos.mpr hpi) (show 0 < (N : ℝ)^2-(k : ℝ)^2 by linarith)
  unfold hillCentralSeparator freeHillValue
  push_cast
  nlinarith

theorem centralSeparator_lt_freeHillValue_sub_margin
    (N n : ℕ) (hN : 2 ≤ N) (hn : N ≤ n) :
    hillCentralSeparator N < freeHillValue n-(n : ℝ)/4 := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hs : (n : ℝ)-(N : ℝ) ≤ (n : ℝ)^2-(N : ℝ)^2 := by
    nlinarith [mul_nonneg (show 0 ≤ (n : ℝ)-(N : ℝ) by linarith)
      (show 0 ≤ (n : ℝ)+(N : ℝ)-1 by linarith)]
  have hpi : 1 ≤ Real.pi^2 := by nlinarith [Real.pi_gt_three]
  have hp := mul_nonneg (sub_nonneg.mpr hpi) (show 0 ≤ (n : ℝ)^2-(N : ℝ)^2 by linarith)
  unfold hillCentralSeparator freeHillValue
  push_cast
  nlinarith

theorem energy_root_central_or_high_of_affine_bound
    (M A b r : ℝ) (N : ℕ) (hM : 0 < M) (hA : 0 ≤ A)
    (hb : 0 ≤ b) (hb8 : b ≤ 1/8) (hbr : b ≤ Real.pi*r/4) (hr : 0 < r)
    (hN : 2 ≤ N) (hNA : 8*A ≤ (N : ℝ)) (hNM : M+A+2 ≤ (N : ℝ))
    (hNAr : 4*A ≤ Real.pi*(N : ℝ)*r)
    (z : ℂ) (hz : ‖z‖ ≤ M ∨ ∃ n : ℕ, ‖z-(freeHillValue n : ℂ)‖ ≤ b*(n : ℝ)+A) :
    -(N : ℝ)^2 < z.re ∧
      (z.re < hillCentralSeparator N ∨ ∃ n : ℕ+, N ≤ (n : ℕ) ∧
        z ∈ ball ((freeHillValue (n : ℕ) : ℝ) : ℂ) (Real.pi*(n : ℕ)*r) ∧
          hillCentralSeparator N < z.re) := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN2 : (N : ℝ) ≤ (N : ℝ)^2 := by nlinarith
  have hpi : 1 ≤ Real.pi^2 := by nlinarith [Real.pi_gt_three]
  rcases hz with hz | ⟨n,hn⟩
  · have hre := abs_le.mp ((abs_re_le_norm z).trans hz)
    have hNsmall := freeHillValue_add_margin_lt_centralSeparator N hN 0 (by omega)
    have hpi9 : 9 < Real.pi^2 := by nlinarith [Real.pi_gt_three]
    have hsep : M < hillCentralSeparator N := by
      unfold hillCentralSeparator freeHillValue
      push_cast
      have hp := mul_pos (sub_pos.mpr hpi9) (show 0 < (N : ℝ)^2 by positivity)
      nlinarith
    exact ⟨by linarith,Or.inl (hre.2.trans_lt hsep)⟩
  have hre : |z.re-freeHillValue n| ≤ b*(n : ℝ)+A := by
    have hh : |z.re-freeHillValue n| ≤ ‖z-(freeHillValue n : ℂ)‖ := by
      simpa only [sub_re,ofReal_re] using abs_re_le_norm (z-(freeHillValue n : ℂ))
    exact hh.trans hn
  have hrange := abs_le.mp hre
  have hbn : b*(n : ℝ) ≤ (n : ℝ)/8 := by nlinarith
  have hfree : (n : ℝ)^2 ≤ freeHillValue n := by
    simpa only [freeHillValue,Int.cast_natCast,one_mul] using mul_le_mul_of_nonneg_right hpi (sq_nonneg (n : ℝ))
  have hlo : -(N : ℝ)^2 < z.re := by
    nlinarith [sq_nonneg ((n : ℝ)-1/16)]
  refine ⟨hlo,?_⟩
  by_cases hnN : n < N
  · left
    have hnR : (n : ℝ) ≤ N := by exact_mod_cast hnN.le
    have hs := freeHillValue_add_margin_lt_centralSeparator N hN n hnN
    linarith
  · right
    have hNn : N ≤ n := le_of_not_gt hnN
    have hnR : (N : ℝ) ≤ n := by exact_mod_cast hNn
    have hnpos : (0 : ℝ) < n := by linarith
    refine ⟨⟨n,by omega⟩,hNn,?_,?_⟩
    · rw [mem_ball,dist_eq_norm]
      change ‖z-(freeHillValue n : ℂ)‖ < Real.pi*(n : ℝ)*r
      have hab : b*(n : ℝ) ≤ Real.pi*(n : ℝ)*r/4 := by nlinarith
      have hAr : 4*A ≤ Real.pi*(n : ℝ)*r := by
        nlinarith [mul_nonneg (show 0 ≤ (n : ℝ)-(N : ℝ) by linarith) (mul_pos Real.pi_pos hr).le]
      exact hn.trans_lt (by nlinarith [mul_pos (mul_pos Real.pi_pos hnpos) hr])
    · have hs := centralSeparator_lt_freeHillValue_sub_margin N n hN hNn
      linarith

end NLS.KdV
