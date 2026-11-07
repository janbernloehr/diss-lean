import NLS.KdV.HillFreeNormalizedAmplitude
import Mathlib.Topology.Order.MonotoneConvergence

/-! The EXACT finite-index free amplitude has a positive uniform lower
bound, so the stronger weighted Fourier symbol grows at infinity. -/
noncomputable section
open Filter Topology Complex
namespace NLS.KdV

theorem hillL2FreeAmplitude_lower (n : ℕ+) : (1/4:ℝ)≤hillL2FreeAmplitude n := by
  apply (sq_le_sq₀ (by norm_num : (0:ℝ)≤1/4) (hillL2FreeAmplitude_pos n).le).mp
  rw [hillL2FreeAmplitude_sq]
  apply (le_div_iff₀ (by positivity : (0:ℝ)<2*Real.pi*(n:ℝ))).mpr
  have h := mul_lt_mul_of_pos_right Real.pi_lt_four (by positivity : (0:ℝ)<n)
  nlinarith

theorem tendsto_hillL2FreeAmplitude_bracket :
    Tendsto (fun k : ℕ => (1+((⟨k+1,Nat.succ_pos k⟩ : ℕ+):ℝ))*hillL2FreeAmplitude ⟨k+1,Nat.succ_pos k⟩) atTop atTop := by
  have ht : Tendsto (fun k : ℕ => ((k:ℝ)+2)/4) atTop atTop :=
    (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop).atTop_div_const (by norm_num)
  apply tendsto_atTop_mono _ ht
  intro k
  have h := mul_le_mul_of_nonneg_left (hillL2FreeAmplitude_lower ⟨k+1,Nat.succ_pos k⟩)
    (by positivity : (0:ℝ)≤1+((⟨k+1,Nat.succ_pos k⟩ : ℕ+):ℝ))
  convert h using 1
  norm_num
  ring

end NLS.KdV
