import NLS.SequenceSpaces.ShiftedHolderDecay
import NLS.SequenceSpaces.CompactPuncturedKernel
import NLS.SequenceSpaces.FiniteExponentTail

/-! One vanishing row bound controls ALL reciprocal off-diagonal
entries of a fixed l2 sequence, including near-neighbor columns. -/
noncomputable section
open Set Complex Filter Topology
open scoped ENNReal Classical
namespace NLS.Coeff

theorem reciprocal_pair_le_shifted_holder_majorant (ρ : Coeff 2) (m k : ℤ) (hkm : k ≠ m) :
    (‖ρ k‖+‖ρ m‖)/‖((k-m:ℤ):ℂ)‖ ≤
      (∑' r : ℤ, ‖ρ r‖*‖shift m (puncturedLattice 2 (by norm_num)) r‖)+‖ρ m‖ := by
  let κ := puncturedLattice 2 (by norm_num : (1:ℝ≥0∞) < 2)
  have hh := lp.tsum_mul_le_mul_norm
    (show (2:ℝ≥0∞).toReal.HolderConjugate (2:ℝ≥0∞).toReal from Real.HolderConjugate.two_two) ρ (shift m κ)
  have hk : ‖ρ k‖/‖((k-m:ℤ):ℂ)‖ ≤ ∑' r : ℤ, ‖ρ r‖*‖shift m κ r‖ := by
    have h := hh.1.sum_le_tsum ({k}:Finset ℤ) (fun _ _ => by positivity)
    simpa only [Finset.sum_singleton,κ,norm_shift_puncturedLattice_apply,if_neg hkm,
      Complex.norm_intCast,div_eq_mul_inv] using h
  have hnorm : ‖((k-m:ℤ):ℂ)‖ = ((k-m).natAbs:ℝ) := by
    rw [Complex.norm_intCast,← Int.cast_abs,← Int.natCast_natAbs]
    simp
  have hpos : 0 < (k-m).natAbs := Int.natAbs_pos.mpr (sub_ne_zero.mpr hkm)
  have hd : 1 ≤ ‖((k-m:ℤ):ℂ)‖ := by rw [hnorm]; exact_mod_cast hpos
  rw [add_div]
  exact add_le_add hk (div_le_self (norm_nonneg _) hd)

theorem exists_uniform_reciprocal_pair_tail (ρ : Coeff 2) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ m : ℤ, N ≤ m.natAbs → ∀ k : ℤ, k ≠ m →
      (‖ρ k‖+‖ρ m‖)/‖((k-m:ℤ):ℂ)‖ < ε := by
  let κ := puncturedLattice 2 (by norm_num : (1:ℝ≥0∞) < 2)
  have ht := (tendsto_tsum_norm_mul_shift_zero (by norm_num) (by norm_num)
    (show (2:ℝ≥0∞).toReal.HolderConjugate (2:ℝ≥0∞).toReal from Real.HolderConjugate.two_two) ρ κ).add
      (tendsto_norm_apply_cofinite (by norm_num) ρ)
  simp only [zero_add] at ht
  obtain ⟨N,hN⟩ := NLS.exists_natAbs_ge_of_eventually_cofinite (ht.eventually_lt_const hε)
  exact ⟨N,fun m hm k hkm => (reciprocal_pair_le_shifted_holder_majorant ρ m k hkm).trans_lt (hN m hm)⟩

end NLS.Coeff
