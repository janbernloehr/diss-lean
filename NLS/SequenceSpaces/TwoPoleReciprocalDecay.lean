import NLS.SequenceSpaces.TwoPoleReciprocalEnvelope
import NLS.SequenceSpaces.ShiftedHolderDecay

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal Classical

namespace NLS.Coeff



/-- The two-pole l1 norm is exactly a separated absolute Hilbert pairing. -/
theorem norm_twoPoleReciprocalEnvelope_eq_shifted_pairing (n : ℤ) :
    ‖twoPoleReciprocalEnvelope n‖ = ∑' m : ℤ,
      ‖puncturedLattice 2 (by norm_num) m‖ *
        ‖shift (-2*n) (puncturedLattice 2 (by norm_num)) m‖ := by
  let a := puncturedLattice 2 (by norm_num)
  have ha (k : ℤ) : a k = (k : ℂ)⁻¹ := by
    by_cases hk : k=0 <;> simp [a,puncturedLattice_apply,hk]
  calc
    _ = ∑' k : ℤ, ‖twoPoleReciprocalEnvelope n k‖ := by
      simpa only [ENNReal.toReal_one,Real.rpow_one] using
        (lp.hasSum_norm (p := 1) (by simp) (twoPoleReciprocalEnvelope n)).tsum_eq.symm
    _ = ∑' m : ℤ, ‖twoPoleReciprocalEnvelope n (m+n)‖ :=
      (Equiv.addRight n).tsum_eq (fun k : ℤ => ‖twoPoleReciprocalEnvelope n k‖) |>.symm
    _ = _ := by
      apply tsum_congr
      intro m
      change ‖twoPoleReciprocalEnvelope n (m+n)‖ = ‖a m‖*‖shift (-2*n) a m‖
      have he : twoPoleReciprocalEnvelope n (m+n) = a m*shift (-2*n) a m := by
        rw [twoPoleReciprocalEnvelope_apply,shift_apply,ha,ha]
        rw [show m+n-n=m by omega,show m+n+n=m-(-2*n) by ring]
      rw [he,norm_mul]

/-- The free l1 majorant tends to zero as the two resonance centers separate. -/
theorem tendsto_norm_twoPoleReciprocalEnvelope_zero :
    Tendsto (fun n : ℕ => ‖twoPoleReciprocalEnvelope n‖) atTop (𝓝 0) := by
  have ht := tendsto_tsum_norm_mul_shift_zero (p := 2) (q := 2) (by simp) (by simp)
    (show (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal from Real.HolderConjugate.two_two)
    (puncturedLattice 2 (by norm_num)) (puncturedLattice 2 (by norm_num))
  have hi : Function.Injective (fun n : ℕ => -2*(n : ℤ)) := by
    intro a b hab
    have hh : (a : ℤ) = (b : ℤ) := mul_left_cancel₀ (by norm_num : (-2 : ℤ) ≠ 0) hab
    exact_mod_cast hh
  have hm : Tendsto (fun n : ℕ => -2*(n : ℤ)) atTop cofinite :=
    hi.tendsto_cofinite.mono_left atTop_le_cofinite
  simpa only [norm_twoPoleReciprocalEnvelope_eq_shifted_pairing,Function.comp_def] using ht.comp hm

end NLS.Coeff
