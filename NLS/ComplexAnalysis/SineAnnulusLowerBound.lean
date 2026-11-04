import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Topology.MetricSpace.ProperSpace.Real

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal

namespace NLS.ComplexAnalysis



theorem exists_uniform_sine_lower_annulus :
    ∃ b : ℝ, 0 < b ∧ ∀ w : ℂ, Real.pi/10 ≤ ‖w‖ → ‖w‖ ≤ Real.pi/2 → b ≤ ‖sin w‖ := by
  let K : Set ℂ := closedBall 0 (Real.pi/2) ∩ {w : ℂ | Real.pi/10 ≤ ‖w‖}
  have hK : IsCompact K := (isCompact_closedBall 0 (Real.pi/2)).inter_right
    (isClosed_le continuous_const continuous_norm)
  have hnonempty : K.Nonempty := by
    refine ⟨(Real.pi/4 : ℝ),?_⟩
    constructor
    · simp only [mem_closedBall,dist_zero_right,norm_real,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < Real.pi/4)]
      linarith [Real.pi_pos]
    · change Real.pi/10 ≤ ‖((Real.pi/4 : ℝ) : ℂ)‖
      rw [norm_real,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < Real.pi/4)]
      linarith [Real.pi_pos]
  have hne (w : ℂ) (hw : w ∈ K) : sin w ≠ 0 := by
    intro hzero
    obtain ⟨k,hk⟩ := Complex.sin_eq_zero_iff.mp hzero
    have hnorm : ‖w‖ = |(k : ℝ)| * Real.pi := by rw [hk,norm_mul,norm_intCast,norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
    have hupper : ‖w‖ ≤ Real.pi/2 := by simpa only [mem_closedBall,dist_zero_right] using hw.1
    have hk0 : |(k : ℝ)| < 1 := by nlinarith [Real.pi_pos]
    have hkint : k = 0 := by
      have h := abs_lt.mp hk0
      have hlow : (-1 : ℤ) < k := by exact_mod_cast h.1
      have hhigh : k < (1 : ℤ) := by exact_mod_cast h.2
      omega
    have hlower : Real.pi/10 ≤ ‖w‖ := hw.2
    rw [hkint,Int.cast_zero,abs_zero,zero_mul] at hnorm
    linarith [Real.pi_pos]
  obtain ⟨w,hw,hmin⟩ := hK.exists_isMinOn hnonempty (Complex.continuous_sin.norm.continuousOn)
  refine ⟨‖sin w‖,norm_pos_iff.mpr (hne w hw),?_⟩
  intro z hlo hhi
  exact hmin ⟨by simpa only [mem_closedBall,dist_zero_right] using hhi,hlo⟩

end NLS.ComplexAnalysis
