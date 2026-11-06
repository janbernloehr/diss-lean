import NLS.KdV.HillComplexPeriodSequence
import NLS.SequenceSpaces.BoundedCoordinateAnalytic

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal

namespace NLS.KdV

variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillComplexScaledPeriodSequence_apply_on (n : ℕ) (hn : 1 ≤ n) (ε D : ℝ) (hD : 0 ≤ D)
    (hc : HillComplexPeriodControl hq hr ε D) (t : Coeff 2 × Coeff 2) (ht : t ∈ univ ×ˢ ball 0 ε)
    (m : ℤ) :
    hillComplexScaledPeriodSequence hq hr n t m = hillComplexScaledPeriodCoordinate hq hr n t m := by
  apply hillComplexScaledPeriodSequence_apply_of_mem
  apply memℓp_hillComplexScaledPeriodCoordinate hq hr n hn t.1 t.2 D hD
  intro k hk hnk
  have hp : ‖t.2‖ ≤ ε := (show ‖t.2‖ < ε by simpa only [mem_ball,dist_zero_right] using ht.2).le
  exact (hc t.2 hp).2 n k hn hk hnk t.1

theorem analyticOnNhd_hillComplexScaledPeriod_coordinate (n : ℕ) (hn : 1 ≤ n) (ε D : ℝ)
    (hD : 0 ≤ D) (hc : HillComplexPeriodControl hq hr ε D) (m : ℤ) :
    AnalyticOnNhd ℂ (fun t : Coeff 2 × Coeff 2 => hillComplexScaledPeriodSequence hq hr n t m)
      (univ ×ˢ ball 0 ε) := by
  have hU : IsOpen ((univ : Set (Coeff 2)) ×ˢ ball (0 : Coeff 2) ε) := isOpen_univ.prod isOpen_ball
  by_cases hm : 0 < m ∧ m ≠ (n : ℤ)
  · have hmt : 1 ≤ m.toNat := by omega
    have hA := analyticOnNhd_hillAbelianComplexPeriod_of_domain 0 hq hr n m.toNat hmt
      (ball 0 ε) isOpen_ball (fun p hp E hE =>
        (hc p (show ‖p‖ ≤ ε from (show ‖p‖ < ε by simpa only [mem_ball,dist_zero_right] using hp).le)).1
          m.toNat hmt E hE)
    have hAmul : AnalyticOnNhd ℂ (fun t : Coeff 2 × Coeff 2 =>
        (((freeHillValue m.toNat : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
          hillAbelianComplexPeriod 0 hq hr n m.toNat t) (univ ×ˢ ball 0 ε) :=
      analyticOnNhd_const.mul hA
    apply AnalyticOnNhd.congr hU hAmul
    intro t ht
    dsimp only []
    rw [hillComplexScaledPeriodSequence_apply_on hq hr n hn ε D hD hc t ht m,
      hillComplexScaledPeriodCoordinate,if_pos hm]
  · apply AnalyticOnNhd.congr hU (show AnalyticOnNhd ℂ (fun _ : Coeff 2 × Coeff 2 => (0 : ℂ))
        (univ ×ˢ ball 0 ε) from analyticOnNhd_const)
    intro t ht
    dsimp only []
    rw [hillComplexScaledPeriodSequence_apply_on hq hr n hn ε D hD hc t ht m,
      hillComplexScaledPeriodCoordinate,if_neg hm]

theorem analyticOnNhd_hillComplexScaledPeriodSequence (n : ℕ) (hn : 1 ≤ n) (ε D : ℝ)
    (hD : 0 ≤ D) (hc : HillComplexPeriodControl hq hr ε D) :
    AnalyticOnNhd ℂ (hillComplexScaledPeriodSequence hq hr n) (univ ×ˢ ball 0 ε) := by
  intro t ht
  let R := ‖t.1‖+1
  let M := Real.exp ((2/Real.pi^2)*R)*R+2*D*Real.exp ((8/Real.pi^2)*R)*ε
  let V : Set (Coeff 2 × Coeff 2) := ball t.1 1 ×ˢ ball 0 ε
  have hcoord (m : ℤ) : AnalyticOnNhd ℂ
      (fun v => hillComplexScaledPeriodSequence hq hr n v m) V :=
    (analyticOnNhd_hillComplexScaledPeriod_coordinate hq hr n hn ε D hD hc m).mono
      (fun _ hv => ⟨mem_univ _,hv.2⟩)
  have hbound (v : Coeff 2 × Coeff 2) (hv : v ∈ V) : ‖hillComplexScaledPeriodSequence hq hr n v‖ ≤ M := by
    have hd : ‖v.1-t.1‖ < 1 := by simpa only [mem_ball,dist_eq_norm] using hv.1
    have hvR : ‖v.1‖ ≤ R := by
      have h := norm_add_le (v.1-t.1) t.1
      rw [sub_add_cancel] at h
      dsimp only [R]
      linarith only [h,hd]
    have hp : ‖v.2‖ ≤ ε := (show ‖v.2‖ < ε by simpa only [mem_ball,dist_zero_right] using hv.2).le
    have hnorm := norm_hillComplexScaledPeriodSequence_le hq hr n hn v.1 v.2 D hD
      (fun k hk hnk => (hc v.2 hp).2 n k hn hk hnk v.1)
    apply hnorm.trans
    apply add_le_add
    · exact mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hvR (by positivity)))
        hvR (norm_nonneg _) (Real.exp_nonneg _)
    · apply mul_le_mul _ hp (norm_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hvR (by positivity))) (by positivity)
  exact Coeff.analyticOnNhd_of_bounded_coordinatewise (hillComplexScaledPeriodSequence hq hr n)
    (isOpen_ball.prod isOpen_ball) hcoord M hbound t ⟨mem_ball_self (by norm_num),ht.2⟩

theorem exists_hillComplexScaledPeriodSequence_analytic_neighborhood :
    ∃ ε D : ℝ, 0 < ε ∧ 0 < D ∧ HillComplexPeriodControl hq hr ε D ∧
      ∀ n : ℕ, 1 ≤ n →
        AnalyticOnNhd ℂ (hillComplexScaledPeriodSequence hq hr n) (univ ×ˢ ball 0 ε) := by
  obtain ⟨ε,D,hε,hD,hc⟩ := exists_hillComplexPeriodControl hq hr
  exact ⟨ε,D,hε,hD,hc,fun n hn => analyticOnNhd_hillComplexScaledPeriodSequence hq hr n hn ε D hD.le hc⟩

end NLS.KdV
