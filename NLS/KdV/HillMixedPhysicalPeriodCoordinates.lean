import NLS.KdV.HillMixedHilbertPeriodMap

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillMixedComplexPeriodSequence_apply_nat
    (N n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (t : Coeff 2 × Coeff 2) :
    hillMixedComplexPeriodSequence q hq hr h0q h0r N n t (k : ℤ) =
      if k ≠ n then (((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
        (if k < N then hillAbelianComplexPeriod q hq hr n k t else hillAbelianComplexPeriod 0 h0q h0r n k t) else 0 := by
  rw [hillMixedComplexPeriodSequence,lp.coeFn_add,Pi.add_apply,
    hillLowComplexPeriodSequence_apply_nat q hq hr N n k hk,
    hillComplexScaledTailPeriodSequence_apply h0q h0r N n hn t (k : ℤ)]
  simp only [Int.natAbs_natCast,hillComplexScaledPeriodCoordinate,Int.toNat_natCast]
  have hkz : (0 : ℤ) < (k : ℤ) := by exact_mod_cast (show 0 < k by omega)
  by_cases hkn : k = n
  · subst k
    simp only [ne_eq,not_true_eq_false,and_false,ite_false,ite_self,add_zero]
  · have hkzn : (k : ℤ) ≠ (n : ℤ) := by exact_mod_cast hkn
    by_cases hkN : k < N
    · simp only [if_pos hkn,if_pos (show k < N ∧ k ≠ n from ⟨hkN,hkn⟩),if_neg (by omega : ¬N ≤ k),if_pos hkN,add_zero]
    · simp only [if_pos hkn,if_neg (by tauto : ¬(k < N ∧ k ≠ n)),
        if_pos (by omega : N ≤ k),if_pos (show (0 : ℤ) < k ∧ (k : ℤ) ≠ n from ⟨hkz,hkzn⟩),if_neg hkN,zero_add]

theorem hillMixedComplexPeriodSequence_apply_unsupported
    (N n : ℕ) (hn : 1 ≤ n) (t : Coeff 2 × Coeff 2) (m : ℤ) (hm : m ≤ 0 ∨ m = (n : ℤ)) :
    hillMixedComplexPeriodSequence q hq hr h0q h0r N n t m = 0 := by
  rw [hillMixedComplexPeriodSequence,lp.coeFn_add,Pi.add_apply,
    hillLowComplexPeriodSequence_apply_unsupported q hq hr N n t m hm,
    hillComplexScaledTailPeriodSequence_apply h0q h0r N n hn t m]
  have hnot : ¬(0 < m ∧ m ≠ (n : ℤ)) := by omega
  simp only [hillComplexScaledPeriodCoordinate,if_neg hnot,ite_self,add_zero]

theorem hillMixedComplexPeriodSequence_at_base_coordinate
    (N n k : ℕ) (hN : 1 ≤ N) (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≠ n) (B D : ℝ)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) (hp : ‖SpectralWeight.one.toCoeff q‖ ≤ B) (a : Coeff 2) :
    hillMixedComplexPeriodSequence q hq hr h0q h0r N n (a,SpectralWeight.one.toCoeff q) (k : ℤ) =
      (((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*hillAbelianHilbertPeriod q hq hr n k a := by
  rw [hillMixedComplexPeriodSequence_apply_nat q hq hr h0q h0r N n k hn hk,if_pos hkn]
  by_cases hkN : k < N
  · rw [if_pos hkN,hillAbelianComplexPeriod_at_base q hq hr n k hk a]
  · rw [if_neg hkN,hillHighAbelianComplexPeriod_eq_intrinsic_physical h0q h0r N hN B D hc q hq hr hp n k (by omega) a]
    rfl

theorem hillMixedComplexPeriodSequence_at_global_roots_eq_zero
    (N n : ℕ) (hN : 1 ≤ N) (hn : 1 ≤ n) (B D : ℝ)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) (hp : ‖SpectralWeight.one.toCoeff q‖ ≤ B)
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr)
    (hperiods : ∀ k : ℕ, 1 ≤ k → k ≠ n → hillAbelianCandidatePeriod q hq hr roots n k = 0) :
    hillMixedComplexPeriodSequence q hq hr h0q h0r N n
      (hillGapRootHilbertCoordinates q hq hr roots hroots,SpectralWeight.one.toCoeff q) = 0 := by
  ext m
  by_cases hm : m ≤ 0 ∨ m = (n : ℤ)
  · exact hillMixedComplexPeriodSequence_apply_unsupported q hq hr h0q h0r N n hn _ m hm
  · have hk : 1 ≤ m.toNat := by omega
    have hkn : m.toNat ≠ n := by omega
    have hcast : (m.toNat : ℤ) = m := by omega
    rw [← hcast,hillMixedComplexPeriodSequence_at_base_coordinate q hq hr h0q h0r N n m.toNat hN hn hk hkn B D hc hp,
      hillAbelianHilbertPeriod_eq_genuine_period q hq hr roots hroots n m.toNat,hperiods m.toNat hk hkn,mul_zero]
    rfl

end NLS.KdV
