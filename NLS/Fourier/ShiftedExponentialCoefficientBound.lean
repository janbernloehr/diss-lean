import NLS.Fourier.ShiftedExponentialFourier
import NLS.Fourier.IntervalCoefficientLinearity

/-! # The pointwise Fourier estimate used in the proof of E.3 -/
noncomputable section
namespace NLS.Fourier

/-- The parity remainder costs at most a factor of two in the shifted bracket. -/
theorem exponential_shift_bracket_le (n m : ℤ) :
    1+|((n-2*m:ℤ):ℝ)| ≤ 2*(1+|((m-n/2:ℤ):ℝ)|) := by
  have hr : n%2 = 0 ∨ n%2 = 1 := by omega
  have hrb : |((n%2:ℤ):ℝ)| ≤ 1 := by rcases hr with h | h <;> simp [h]
  have hi : n-2*m = n%2-2*(m-n/2) := by omega
  rw [hi]
  push_cast
  have h := norm_sub_le ((n%2:ℤ):ℝ) (2*((m:ℝ)-(n/2:ℤ)))
  simp only [Real.norm_eq_abs] at h
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at h
  linarith

/-- Literal Fourier integrals have the reciprocal decay displayed in E.3's proof. -/
theorem norm_intervalFourierCoefficient_exponential_near_lattice (n m : ℤ) (z : ℂ)
    (hz : ‖z-(Real.pi:ℂ)*n‖ ≤ Real.pi/4) :
    ‖intervalFourierCoefficient 1 (unitIntervalExponential z) m‖ ≤
      (2*((2+5*Real.pi/4)*Real.exp (5*Real.pi/4)))/(1+|((n-2*m:ℤ):ℝ)|) := by
  let B : ℝ := 5*Real.pi/4
  let w : ℂ := z-2*(Real.pi:ℂ)*(n/2:ℤ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hw : ‖w‖ ≤ B := norm_exponential_residual_frequency_le n z hz
  have hmod := intervalFourierCoefficient_exponential_modulation w (n/2) m
  dsimp only [w] at hmod
  rw [sub_add_cancel] at hmod
  rw [hmod]
  have hbound := norm_unitIntervalFourierCoefficient_le_bracket (unitIntervalExponential w)
    (contDiff_unitIntervalExponential w) (Real.exp B) (B*Real.exp B)
    (Real.exp_pos B).le (by positivity)
    (fun x hx => (unitIntervalExponential_bounds w hB hw x hx).1)
    (fun x hx => (unitIntervalExponential_bounds w hB hw x hx).2) (m-n/2)
  have hnum : 2*Real.exp B+B*Real.exp B = (2+B)*Real.exp B := by ring
  rw [hnum] at hbound
  apply hbound.trans
  change ((2+B)*Real.exp B)/(1+|((m-n/2:ℤ):ℝ)|) ≤
    (2*((2+B)*Real.exp B))/(1+|((n-2*m:ℤ):ℝ)|)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have h := exponential_shift_bracket_le n m
  have hK : 0 ≤ (2+B)*Real.exp B := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h hK]

/-- The exact difference in the printed proof has a common reciprocal-decay constant. -/
theorem norm_intervalFourierCoefficient_exponential_difference (n m : ℤ) (z : ℂ)
    (hz : ‖z-(Real.pi:ℂ)*n‖ ≤ Real.pi/4) :
    ‖intervalFourierCoefficient 1
      (fun x => unitIntervalExponential z x-unitIntervalExponential ((Real.pi:ℂ)*n) x) m‖ ≤
      (4*((2+5*Real.pi/4)*Real.exp (5*Real.pi/4)))/(1+|((n-2*m:ℤ):ℝ)|) := by
  rw [intervalFourierCoefficient_sub 1 _ _ (contDiff_unitIntervalExponential z).continuous
    (contDiff_unitIntervalExponential ((Real.pi:ℂ)*n)).continuous]
  have h1 := norm_intervalFourierCoefficient_exponential_near_lattice n m z hz
  have h2 := norm_intervalFourierCoefficient_exponential_near_lattice n m ((Real.pi:ℂ)*n)
    (by simp only [sub_self,norm_zero]; positivity)
  apply (norm_sub_le _ _).trans ((add_le_add h1 h2).trans_eq _)
  ring

end NLS.Fourier
