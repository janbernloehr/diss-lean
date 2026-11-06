import NLS.Articles.KdVKdV2Frequencies.GlobalRoughGroundEnergyBound
import NLS.ZakharovShabat.SourceHilbertWeakActionComparison

/-! # Uniform ordinary ground-factor action tails in the actual weak target

The norm-ball Dirac comparison is calibrated by the ORIGINAL physical
Hill actions of the SAME global map. Spectral reflection retains BOTH
signs. The cutoff depends only on the actual factor pair norm bound.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.KdV NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

/-- High positive ordinary actions of EVERY actual normalized factor
are controlled uniformly by the actual positive weak target coefficients. -/
theorem exists_uniform_ground_ordinary_positive_action_bound (D : GlobalRoughAbelianForwardData)
    (R : ℝ) : ∃ N : ℕ, 1≤N ∧
      ∀ (p : RealPeriodOneHillPotential) (u : PeriodOneRealL2) (e : ℝ), u.val 0=0 →
      periodOneMiura u.val=hillOriginalHminusSource p.val+
        periodOneL2Inclusion (lp.single 2 0 (e : ℂ)) → ‖hillMiuraDiagonal u.val‖≤R →
      ∀ n : ℕ, N≤n →
        (sourceRealAction (by simp) (by norm_num) (hillMiuraRealSource u).val (hillMiuraRealSource u).property n).re ≤
          (2/Real.pi)*‖D.positive (hillOriginalHminusSource p.val) n‖^2 := by
  obtain ⟨N,hN,hbound⟩ := exists_uniform_real_hilbert_ordinary_action_comparison R
  refine ⟨N,hN,?_⟩
  intro p u e hu hi hnorm n hn
  have h := hbound (hillMiuraRealSource u) hnorm n hn
  have hact := hillOriginal_action_eq_twice_ground_Dirac p u e hu hi n (by omega)
  rw [←hact,D.positive_physical_action_norm p n (by omega)] at h
  have hnR : (1 : ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hn0 : 0<(n : ℝ) := by exact_mod_cast (show 0<n by omega)
  apply h.trans
  calc
    _ ≤ (2*(n : ℝ))*‖D.positive (hillOriginalHminusSource p.val) n‖^2/(Real.pi*(n : ℝ)) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)) (by positivity)
    _ = _ := by field_simp

/-- A single cutoff controls BOTH signed ordinary action tails by the
SAME actual weak target. No uniform stronger Sobolev bound is assumed. -/
theorem exists_uniform_ground_ordinary_signed_action_bound (D : GlobalRoughAbelianForwardData)
    (R : ℝ) : ∃ N : ℕ, 1≤N ∧
      ∀ (p : RealPeriodOneHillPotential) (u : PeriodOneRealL2) (e : ℝ), u.val 0=0 →
      periodOneMiura u.val=hillOriginalHminusSource p.val+
        periodOneL2Inclusion (lp.single 2 0 (e : ℂ)) → ‖hillMiuraDiagonal u.val‖≤R →
      ∀ j : ℤ, N≤j.natAbs →
        (sourceRealAction (by simp) (by norm_num) (hillMiuraRealSource u).val (hillMiuraRealSource u).property j).re ≤
          (2/Real.pi)*(‖D.positive (hillOriginalHminusSource p.val) j‖^2+
            ‖D.positive (hillOriginalHminusSource p.val) (-j)‖^2) := by
  obtain ⟨N,hN,hbound⟩ := D.exists_uniform_ground_ordinary_positive_action_bound R
  refine ⟨N,hN,?_⟩
  intro p u e hu hi hnorm j hj
  have hp := hbound p u e hu hi hnorm
  rcases lt_trichotomy j 0 with hneg|hzero|hpos
  · let n := (-j).toNat
    have hnj : (n : ℤ)=-j := by dsimp only [n]; omega
    have hn : N≤n := by dsimp only [n]; omega
    have he := hillMiura_realHigherAction_neg u (n : ℤ) 0
    simp only [pow_zero,one_mul,sourceRealHigherAction_zero] at he
    have hje : j=-(n : ℤ) := by omega
    rw [hje,he,neg_neg]
    exact (hp n hn).trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left (sq_nonneg _)) (by positivity))
  · subst j; simp only [Int.natAbs_zero] at hj; omega
  · let n := j.toNat
    have hnj : (n : ℤ)=j := by dsimp only [n]; omega
    have hn : N≤n := by dsimp only [n]; omega
    have h := hp n hn
    rw [hnj] at h
    exact h.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg _)) (by positivity))

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
