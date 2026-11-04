import NLS.KdV.HillWeightedColumnNumeratorBound
import NLS.KdV.HillFreeInteractionKernel

/-! The original signed frequency separation gives quadratic energy
separation, with the inverse-index column weight kept exactly. One
constant works before all distinct positive row and column indices. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

theorem hillPlacedEnergy_difference_ne_zero
    {V : Set (CoeffPair 2)} {D : ℤ → Set ℂ} {C : ℝ}
    (hD : SourceIsolatingNeighborhoods (by norm_num) (by norm_num) V D C)
    (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2)
    (hplace : ∀ k : ℤ, hillIndependentFrequency t k ∈ D k)
    (m r : ℕ+) (hrm : r ≠ m) (z : ℂ) (hz : z ∈ closure (D ((m:ℕ):ℤ))) :
    hillEnergySequenceZero r t.2-(z^2-t.1) ≠ 0 := by
  have hmr : ((m:ℕ):ℤ) ≠ ((r:ℕ):ℤ) := by
    intro h
    exact hrm (Subtype.ext (Int.ofNat.inj h.symm))
  have hs := hD.weighted_separation_closure ((r:ℕ):ℤ) ((m:ℕ):ℤ) hmr
    (hillIndependentFrequency t ((r:ℕ):ℤ)) (hplace _) z hz
  have hp := (hillIndependent_multiplier_bound hD t hplace r m z hz).1
  have he : hillEnergySequenceZero r t.2-(z^2-t.1) =
      (hillIndependentFrequency t ((r:ℕ):ℤ)-z)*(hillIndependentFrequency t ((r:ℕ):ℤ)+z) := by
    rw [show (hillIndependentFrequency t ((r:ℕ):ℤ)-z)*(hillIndependentFrequency t ((r:ℕ):ℤ)+z) =
      hillIndependentFrequency t ((r:ℕ):ℤ)^2-z^2 by ring, hillIndependentFrequency_positive_sq t r]
    ring
  rw [he]
  exact mul_ne_zero (sub_ne_zero.mpr hs.1.symm) hp

theorem hillPlacedEnergy_quadratic_ratio_bound
    {V : Set (CoeffPair 2)} {D : ℤ → Set ℂ} {C : ℝ}
    (hD : SourceIsolatingNeighborhoods (by norm_num) (by norm_num) V D C)
    (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2)
    (hplace : ∀ k : ℤ, hillIndependentFrequency t k ∈ D k)
    (m r : ℕ+) (hrm : r ≠ m) (z : ℂ) (hz : z ∈ closure (D ((m:ℕ):ℤ))) :
    ‖((((r:ℕ):ℂ)^2-((m:ℕ):ℂ)^2)/(hillEnergySequenceZero r t.2-(z^2-t.1)))‖ ≤ C^2 := by
  have hmr : ((m:ℕ):ℤ) ≠ ((r:ℕ):ℤ) := by
    intro h
    exact hrm (Subtype.ext (Int.ofNat.inj h.symm))
  have hs := hD.weighted_separation_closure ((r:ℕ):ℤ) ((m:ℕ):ℤ) hmr
    (hillIndependentFrequency t ((r:ℕ):ℤ)) (hplace _) z hz
  have hp := (hillIndependent_multiplier_bound hD t hplace r m z hz).1
  have hm : ‖((((r:ℕ):ℂ)-((m:ℕ):ℂ))/(hillIndependentFrequency t ((r:ℕ):ℤ)-z))‖ ≤ C := by
    simpa only [norm_div,Int.cast_sub,Int.cast_natCast] using hs.2
  have hplus := hillIndependent_sum_index_ratio_bound hD t hplace r m z hz
  have he : (((r:ℕ):ℂ)^2-((m:ℕ):ℂ)^2)/(hillEnergySequenceZero r t.2-(z^2-t.1)) =
      ((((r:ℕ):ℂ)-((m:ℕ):ℂ))/(hillIndependentFrequency t ((r:ℕ):ℤ)-z))*
        ((((r:ℕ):ℂ)+((m:ℕ):ℂ))/(hillIndependentFrequency t ((r:ℕ):ℤ)+z)) := by
    have hd : hillEnergySequenceZero r t.2-(z^2-t.1) =
        (hillIndependentFrequency t ((r:ℕ):ℤ)-z)*(hillIndependentFrequency t ((r:ℕ):ℤ)+z) := by
      rw [show (hillIndependentFrequency t ((r:ℕ):ℤ)-z)*(hillIndependentFrequency t ((r:ℕ):ℤ)+z) =
        hillIndependentFrequency t ((r:ℕ):ℤ)^2-z^2 by ring,hillIndependentFrequency_positive_sq t r]
      ring
    rw [hd]
    field_simp [sub_ne_zero.mpr hs.1.symm,hp]
    ring
  rw [he,norm_mul]
  exact (mul_le_mul hm hplus (norm_nonneg _) (zero_le_one.trans hD.one_le)).trans_eq (pow_two C).symm

theorem hillPlacedEnergy_inverse_index_kernel_bound
    {V : Set (CoeffPair 2)} {D : ℤ → Set ℂ} {C : ℝ}
    (hD : SourceIsolatingNeighborhoods (by norm_num) (by norm_num) V D C)
    (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2)
    (hplace : ∀ k : ℤ, hillIndependentFrequency t k ∈ D k)
    (m r : ℕ+) (hrm : r ≠ m) (z : ℂ) (hz : z ∈ closure (D ((m:ℕ):ℤ))) :
    ‖((r:ℕ):ℂ)/(hillEnergySequenceZero r t.2-(z^2-t.1))‖ ≤
      Real.pi^2*C^2*‖hillFreeInteractionKernel m ((r:ℕ):ℤ)‖ := by
  have hq := hillPlacedEnergy_quadratic_ratio_bound hD t hplace m r hrm z hz
  have he : ((r:ℕ):ℂ)/(hillEnergySequenceZero r t.2-(z^2-t.1)) =
      (Real.pi:ℂ)^2*hillFreeInteractionKernel m ((r:ℕ):ℤ)*
        ((((r:ℕ):ℂ)^2-((m:ℕ):ℂ)^2)/(hillEnergySequenceZero r t.2-(z^2-t.1))) := by
    rw [hillFreeInteractionKernel_positive m r hrm]
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero,sub_ne_zero.mpr (pnat_complex_squares_ne hrm)]
  rw [he,norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
  calc
    _ ≤ (Real.pi^2*‖hillFreeInteractionKernel m ((r:ℕ):ℤ)‖)*C^2 :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    _ = _ := by ring

end NLS.KdV
