import NLS.KdV.HillL2SheetRootFourierEstimate
import NLS.KdV.HillDirichletFrequencyDisplacement

/-! # Fourier control at the actual complex moving Dirichlet zero -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillDirichletSheetRoot_moving_fourier_bound (k : ℕ+) (u : Coeff 2) (E : ℂ)
    (hu : ‖u‖ ≤ 1/(16*Real.exp 1))
    (hE : ‖E-freeHillEnergy k‖ ≤ (k : ℝ)/16)
    (hzero : hillL2DirichletCharacteristic (Coeff.periodDouble u) E = 0) :
    (k : ℝ)*‖hillDirichletSheetRoot (Coeff.periodDouble u) E‖ ≤
      (‖u (-(k : ℤ))‖+‖u (k : ℤ)‖)/2+32*(Real.exp 1)^3*‖u‖^2/(k : ℝ) := by
  obtain ⟨hzlo,_,hδhalf,hδ⟩ := hillDirichlet_frequency_displacement_bound k (Coeff.periodDouble u) E
    (by simpa only [Coeff.norm_periodDouble] using hu) hE hzero
  rw [Coeff.norm_periodDouble] at hδ
  have hkp : (0 : ℝ) < k := by positivity
  have hzn : 0 < ‖sqrt E‖ := hkp.trans_le hzlo
  have hsmall : 4*Real.exp 1*‖u‖ ≤ ‖sqrt E‖ := by
    have h := (le_div_iff₀ (by positivity : 0 < 16*Real.exp 1)).mp hu
    have hk : (1 : ℝ) ≤ k := by exact_mod_cast k.property
    nlinarith
  have hr := hillL2SheetRoot_fourier_remainder_bound u (k : ℕ) (sqrt E)
    (norm_pos_iff.mp hzn) (by simpa only [mul_comm] using hδhalf.trans (by norm_num : (1/2 : ℝ) ≤ 1)) hsmall
  rw [sq_sqrt] at hr
  have hd : ‖sqrt E-(k : ℂ)*Real.pi‖ ≤ 8*(Real.exp 1)^2*‖u‖/(k : ℝ) := by
    simpa only [mul_comm] using hδ
  have hrem : ‖sqrt E*hillDirichletSheetRoot (Coeff.periodDouble u) E-
      (-1 : ℂ)^(k : ℕ)*(u (-(k : ℤ))-u (k : ℤ))/(2*I)‖ ≤ 32*(Real.exp 1)^3*‖u‖^2/(k : ℝ) := by
    apply hr.trans
    calc
      _ ≤ 16*(Real.exp 1)^3*‖u‖^2/(k : ℝ)+
          2*Real.exp 1*(8*(Real.exp 1)^2*‖u‖/(k : ℝ))*‖u‖ := by gcongr
      _ = _ := by ring
  have hlead : ‖(-1 : ℂ)^(k : ℕ)*(u (-(k : ℤ))-u (k : ℤ))/(2*I)‖ ≤
      (‖u (-(k : ℤ))‖+‖u (k : ℤ)‖)/2 := by
    simp only [norm_div,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,norm_ofNat,norm_I,mul_one]
    exact div_le_div_of_nonneg_right (norm_sub_le _ _) (by norm_num)
  have h := norm_le_norm_sub_add (sqrt E*hillDirichletSheetRoot (Coeff.periodDouble u) E)
    ((-1 : ℂ)^(k : ℕ)*(u (-(k : ℤ))-u (k : ℤ))/(2*I))
  rw [norm_mul] at h
  exact (mul_le_mul_of_nonneg_right hzlo (norm_nonneg _)).trans
    (h.trans ((add_le_add hrem hlead).trans_eq (by ring)))

end NLS.KdV
