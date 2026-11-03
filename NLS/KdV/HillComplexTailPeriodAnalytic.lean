import NLS.KdV.HillComplexTailPeriodSequence

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

def HillComplexTailPeriodControl (N : ℕ) (B D : ℝ) : Prop :=
  ∀ p : Coeff 2, ‖p‖ ≤ B →
    (∀ k : ℕ, N ≤ k → ∀ E ∈ sphere (hillRealGapCenter 0 hq hr k : ℂ)
      (hillRealGapHalfLength 0 hq hr k+hillRealGapCollar 0 hq hr k),
      (E,p) ∈ hillAbelianComplexRootDomain 0 hq hr) ∧
    ∀ n k : ℕ, 1 ≤ n → N ≤ k → n ≠ k → ∀ a : Coeff 2,
      ‖(((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
        (hillAbelianComplexPeriod 0 hq hr n k (a,p)-hillAbelianHilbertPeriod 0 hq hr n k a)‖ ≤
        D*Real.exp ((8/Real.pi^2)*‖a‖)*‖p‖/(k : ℝ)

theorem exists_hillComplexTailPeriodControl (B : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ D : ℝ, 0 < D ∧ HillComplexTailPeriodControl hq hr N B D :=
  exists_hillAbelianComplexPeriod_bounded_tail_control hq hr B

theorem analyticOnNhd_hillComplexScaledTailPeriod_coordinate
    (N n : ℕ) (hN : 1 ≤ N) (hn : 1 ≤ n) (B D : ℝ)
    (hc : HillComplexTailPeriodControl hq hr N B D) (m : ℤ) :
    AnalyticOnNhd ℂ (fun t : Coeff 2 × Coeff 2 => hillComplexScaledTailPeriodSequence hq hr N n t m)
      (univ ×ˢ ball 0 B) := by
  have hU : IsOpen ((univ : Set (Coeff 2)) ×ˢ ball (0 : Coeff 2) B) := isOpen_univ.prod isOpen_ball
  by_cases hcut : N ≤ m.natAbs
  · by_cases hm : 0 < m ∧ m ≠ (n : ℤ)
    · have hmt : N ≤ m.toNat := by omega
      have hA := analyticOnNhd_hillAbelianComplexPeriod_of_domain 0 hq hr n m.toNat (hN.trans hmt)
        (ball 0 B) isOpen_ball (fun p hp E hE =>
          (hc p (show ‖p‖ ≤ B from (show ‖p‖ < B by simpa only [mem_ball,dist_zero_right] using hp).le)).1 m.toNat hmt E hE)
      have hmul : AnalyticOnNhd ℂ (fun t : Coeff 2 × Coeff 2 =>
          (((freeHillValue m.toNat : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*hillAbelianComplexPeriod 0 hq hr n m.toNat t)
          (univ ×ˢ ball 0 B) := analyticOnNhd_const.mul hA
      apply AnalyticOnNhd.congr hU hmul
      intro t _
      dsimp only []
      rw [hillComplexScaledTailPeriodSequence_apply hq hr N n hn t m,if_pos hcut,
        hillComplexScaledPeriodCoordinate,if_pos hm]
    · apply AnalyticOnNhd.congr hU (show AnalyticOnNhd ℂ (fun _ : Coeff 2 × Coeff 2 => (0 : ℂ))
        (univ ×ˢ ball 0 B) from analyticOnNhd_const)
      intro t _
      dsimp only []
      rw [hillComplexScaledTailPeriodSequence_apply hq hr N n hn t m,if_pos hcut,
        hillComplexScaledPeriodCoordinate,if_neg hm]
  · apply AnalyticOnNhd.congr hU (show AnalyticOnNhd ℂ (fun _ : Coeff 2 × Coeff 2 => (0 : ℂ))
        (univ ×ˢ ball 0 B) from analyticOnNhd_const)
    intro t _
    dsimp only []
    rw [hillComplexScaledTailPeriodSequence_apply hq hr N n hn t m,if_neg hcut]

theorem analyticOnNhd_hillComplexScaledTailPeriodSequence
    (N n : ℕ) (hN : 1 ≤ N) (hn : 1 ≤ n) (B D : ℝ) (hD : 0 ≤ D)
    (hc : HillComplexTailPeriodControl hq hr N B D) :
    AnalyticOnNhd ℂ (hillComplexScaledTailPeriodSequence hq hr N n) (univ ×ˢ ball 0 B) := by
  intro t ht
  let R := ‖t.1‖+1
  let M := Real.exp ((2/Real.pi^2)*R)*R+2*D*Real.exp ((8/Real.pi^2)*R)*B
  let V : Set (Coeff 2 × Coeff 2) := ball t.1 1 ×ˢ ball 0 B
  have hcoord (m : ℤ) : AnalyticOnNhd ℂ (fun v => hillComplexScaledTailPeriodSequence hq hr N n v m) V :=
    (analyticOnNhd_hillComplexScaledTailPeriod_coordinate hq hr N n hN hn B D hc m).mono
      (fun _ hv => ⟨mem_univ _,hv.2⟩)
  have hbound (v : Coeff 2 × Coeff 2) (hv : v ∈ V) : ‖hillComplexScaledTailPeriodSequence hq hr N n v‖ ≤ M := by
    have hd : ‖v.1-t.1‖ < 1 := by simpa only [mem_ball,dist_eq_norm] using hv.1
    have hvR : ‖v.1‖ ≤ R := by
      have h := norm_add_le (v.1-t.1) t.1
      rw [sub_add_cancel] at h
      dsimp only [R]
      linarith only [h,hd]
    have hp : ‖v.2‖ ≤ B := (show ‖v.2‖ < B by simpa only [mem_ball,dist_zero_right] using hv.2).le
    have hnorm := norm_hillComplexScaledTailPeriodSequence_le hq hr N n hn v.1 v.2 D hD
      (fun k hk hnk => (hc v.2 hp).2 n k hn hk hnk v.1)
    apply hnorm.trans
    apply add_le_add
    · exact mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hvR (by positivity)))
        hvR (norm_nonneg _) (Real.exp_nonneg _)
    · apply mul_le_mul _ hp (norm_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hvR (by positivity))) (by positivity)
  exact Coeff.analyticOnNhd_of_bounded_coordinatewise (hillComplexScaledTailPeriodSequence hq hr N n)
    (isOpen_ball.prod isOpen_ball) hcoord M hbound t ⟨mem_ball_self (by norm_num),ht.2⟩

theorem exists_hillComplexScaledTailPeriodSequence_analytic_on_bounded_potentials (B : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, 1 ≤ n →
      AnalyticOnNhd ℂ (hillComplexScaledTailPeriodSequence hq hr N n) (univ ×ˢ ball 0 B) := by
  obtain ⟨N,hN,D,hD,hcontrol⟩ := exists_hillComplexTailPeriodControl hq hr B
  exact ⟨N,hN,fun n hn => analyticOnNhd_hillComplexScaledTailPeriodSequence hq hr N n hN hn B D hD.le hcontrol⟩

end NLS.KdV
