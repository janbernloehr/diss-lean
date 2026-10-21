import NLS.Fourier.ContinuousSynthesis
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # Actual increment estimates for the phase n log n -/
noncomputable section
set_option autoImplicit false
open Set Real
namespace NLS.Fourier

def chirpPhase (x : ℝ) : ℝ := x*Real.log x

def chirpPhaseIncrement (x : ℝ) : ℝ := chirpPhase (x+1)-chirpPhase x

theorem hasDerivAt_chirpPhase (x : ℝ) (hx : 0 < x) :
    HasDerivAt chirpPhase (Real.log x+1) x := by
  change HasDerivAt (fun y : ℝ => y*Real.log y) (Real.log x+1) x
  convert! (hasDerivAt_id x).mul (Real.hasDerivAt_log hx.ne') using 1
  simp [hx.ne']

theorem hasDerivAt_chirpPhaseIncrement (x : ℝ) (hx : 0 < x) :
    HasDerivAt chirpPhaseIncrement (Real.log (x+1)-Real.log x) x := by
  change HasDerivAt (fun y : ℝ => chirpPhase (y+1)-chirpPhase y)
    (Real.log (x+1)-Real.log x) x
  convert! ((hasDerivAt_chirpPhase (x+1) (by linarith)).comp x
    ((hasDerivAt_id x).add_const 1)).sub (hasDerivAt_chirpPhase x hx) using 1
  simp

theorem chirpPhaseIncrement_derivative_bounds (x : ℝ) (hx : 0 < x) :
    1/(x+1) ≤ Real.log (x+1)-Real.log x ∧
      Real.log (x+1)-Real.log x ≤ 1/x := by
  have hr : 0 < (x+1)/x := div_pos (by linarith) hx
  have hlo := Real.one_sub_inv_le_log_of_pos hr
  have hhi := Real.log_le_sub_one_of_pos hr
  rw [Real.log_div (by linarith : x+1 ≠ 0) hx.ne'] at hlo hhi
  have he₁ : 1-((x+1)/x)⁻¹ = 1/(x+1) := by field_simp; ring
  have he₂ : (x+1)/x-1 = 1/x := by field_simp; ring
  exact ⟨by simpa only [he₁] using hlo,by simpa only [he₂] using hhi⟩

theorem antitoneOn_chirpPhaseIncrement_derivative :
    AntitoneOn (fun x : ℝ => Real.log (x+1)-Real.log x) (Ioi 0) := by
  intro x hx y hy hxy
  have he (t : ℝ) (ht : 0 < t) :
      Real.log (t+1)-Real.log t = Real.log (1+1/t) := by
    rw [← Real.log_div (by linarith : t+1 ≠ 0) ht.ne']
    congr 1
    field_simp
  change Real.log (y+1)-Real.log y ≤ Real.log (x+1)-Real.log x
  rw [he x hx,he y hy]
  apply Real.log_le_log (by have : 0 < y := hy; positivity)
  exact add_le_add_right (one_div_le_one_div_of_le hx hxy) 1

/-- Exact increment bounds for the correlation phase, for every positive shift. -/
theorem chirpPhaseIncrement_shift_bounds (x h : ℝ) (hx : 0 < x) (hh : 0 < h) :
    h/(x+h+1) ≤ chirpPhaseIncrement (x+h)-chirpPhaseIncrement x ∧
      chirpPhaseIncrement (x+h)-chirpPhaseIncrement x ≤ h/x := by
  have hd (t : ℝ) (ht : t ∈ Icc x (x+h)) :=
    hasDerivAt_chirpPhaseIncrement t (lt_of_lt_of_le hx ht.1)
  obtain ⟨c,hc,he⟩ := exists_hasDerivAt_eq_slope chirpPhaseIncrement
    (fun t => Real.log (t+1)-Real.log t) (show x < x+h by linarith)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => hd t ⟨ht.1.le,ht.2.le⟩)
  have hcp : 0 < c := lt_trans hx hc.1
  have hb := chirpPhaseIncrement_derivative_bounds c hcp
  have hlo : 1/(x+h+1) ≤ Real.log (c+1)-Real.log c :=
    (one_div_le_one_div_of_le (by linarith : 0 < c+1) (by linarith [hc.2])).trans hb.1
  have hhi : Real.log (c+1)-Real.log c ≤ 1/x :=
    hb.2.trans (one_div_le_one_div_of_le hx hc.1.le)
  have he' : chirpPhaseIncrement (x+h)-chirpPhaseIncrement x =
      (Real.log (c+1)-Real.log c)*h := by
    rw [show x+h-x = h by ring] at he
    exact ((eq_div_iff hh.ne').mp he).symm
  rw [he']
  constructor
  · simpa only [div_eq_mul_inv,one_mul,mul_one,mul_comm] using mul_le_mul_of_nonneg_right hlo hh.le
  · simpa only [div_eq_mul_inv,one_mul,mul_one,mul_comm] using mul_le_mul_of_nonneg_right hhi hh.le

/-- Correlation increments decrease as the block position increases. -/
theorem antitoneOn_chirpPhaseIncrement_shift (h : ℝ) (hh : 0 ≤ h) :
    AntitoneOn (fun x => chirpPhaseIncrement (x+h)-chirpPhaseIncrement x) (Ioi 0) := by
  have hd (x : ℝ) (hx : 0 < x) :
      HasDerivAt (fun x => chirpPhaseIncrement (x+h)-chirpPhaseIncrement x)
        ((Real.log (x+h+1)-Real.log (x+h))-(Real.log (x+1)-Real.log x)) x := by
    convert! ((hasDerivAt_chirpPhaseIncrement (x+h) (by linarith)).comp x
      ((hasDerivAt_id x).add_const h)).sub (hasDerivAt_chirpPhaseIncrement x hx) using 1
    simp
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  · exact fun x hx => (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : 0 < x := interior_subset hx
    rw [(hd x hx').deriv]
    exact sub_nonpos.mpr (antitoneOn_chirpPhaseIncrement_derivative hx'
      (show 0 < x+h by linarith) (by linarith))

/-- On a dyadic block, every positive correlation lag stays away from resonance. -/
theorem chirpPhaseIncrement_half_shift_bounds (N x h : ℝ)
    (hN : 1 ≤ N) (hx : N ≤ x) (hxh : x+h ≤ 2*N) (hh : 0 < h) (hhN : h ≤ N) :
    h/(6*N) ≤ (chirpPhaseIncrement (x+h)-chirpPhaseIncrement x)/2 ∧
      (chirpPhaseIncrement (x+h)-chirpPhaseIncrement x)/2 ≤ 1/2 := by
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hxp : 0 < x := hNp.trans_le hx
  have hb := chirpPhaseIncrement_shift_bounds x h hxp hh
  have hlo : h/(3*N) ≤ h/(x+h+1) :=
    div_le_div_of_nonneg_left hh.le (by linarith) (by linarith)
  have hhi : h/x ≤ 1 := (div_le_one hxp).mpr (hhN.trans hx)
  constructor
  · have he : h/(6*N) = (h/(3*N))/2 := by ring
    rw [he]
    exact div_le_div_of_nonneg_right (hlo.trans hb.1) (by norm_num)
  · exact div_le_div_of_nonneg_right (hb.2.trans hhi) (by norm_num)

end NLS.Fourier
