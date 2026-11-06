import NLS.ComplexAnalysis.HilbertWeakWeightLimits
import NLS.KdV.HillFreeSeparatedWeights
import NLS.SequenceSpaces.ShiftedHolderDecay

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



theorem tendsto_hillFreeSeparatedWeight_coordinate (n : ℕ) (m : ℤ) :
    Tendsto (fun k : ℕ => hillFreeSeparatedWeight n k m) atTop (𝓝 0) := by
  have hi : Function.Injective (fun k : ℕ => m-(k : ℤ)) := by
    intro k j he
    have hh : (k : ℤ) = (j : ℤ) := sub_right_injective he
    exact_mod_cast hh
  have ht := (Coeff.tendsto_norm_apply_cofinite (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    (Coeff.puncturedLattice 2 (by norm_num))).comp hi.tendsto_cofinite
  rw [Nat.cofinite_eq_atTop] at ht
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun k => norm_nonneg _) _
    (show Tendsto (fun k : ℕ => ((Real.pi^2)⁻¹)*‖Coeff.puncturedLattice 2 (by norm_num) (m-(k : ℤ))‖) atTop (𝓝 0) by
      simpa only [mul_zero, Function.comp_def] using ht.const_mul ((Real.pi^2)⁻¹))
  intro k
  have hb := hillFreeSeparatedWeightSymbol_bound n k m
  simpa only [hillFreeSeparatedWeight,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,Coeff.shift_apply,
    norm_mul,norm_inv,norm_pow,norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos] using hb

theorem tendsto_hilbertWeightedProduct_hillFreeSeparatedWeight (n : ℕ) (a : Coeff 2) :
    Tendsto (fun k : ℕ => hilbertWeightedProduct (hillFreeSeparatedWeight n k) a) atTop (𝓝 1) :=
  tendsto_hilbertWeightedProduct_of_bounded_weak_weights (hillFreeSeparatedWeight n)
    (2/Real.pi^2) (norm_hillFreeSeparatedWeight_le n) (tendsto_hillFreeSeparatedWeight_coordinate n) a

end NLS.KdV
