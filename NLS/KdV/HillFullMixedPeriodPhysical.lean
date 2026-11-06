import NLS.KdV.HillFullMixedPeriodMap
import NLS.KdV.HillHighProductPeriodMatching

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillFullMixedComplexPeriodSequence_at_base_coordinate
    (N k : ℕ) (hN : 1 ≤ N) (hk : 1 ≤ k) (B D : ℝ) (hD : 0 ≤ D)
    (hc : HillComplexTailPeriodControl h0q h0r N B D)
    (hp : ‖SpectralWeight.one.toCoeff q‖ ≤ B) (a : Coeff 2) :
    hillFullMixedComplexPeriodSequence q hq hr h0q h0r N (a,SpectralWeight.one.toCoeff q) (k : ℤ) =
      (-2*(Real.pi : ℂ))*hillAbelianProductComplexPeriod q hq hr 0 k (a,SpectralWeight.one.toCoeff q) := by
  rw [hillFullMixedComplexPeriodSequence_apply_nat q hq hr h0q h0r N k hN hk B D hD hc a _ hp]
  by_cases hkN : k < N
  · rw [if_pos hkN]
  · rw [if_neg hkN,hillHighAbelianProductComplexPeriod_eq_intrinsic_physical h0q h0r N hN B D hc q hq hr hp 0 k (by omega) a,
      hillAbelianProductComplexPeriod_at_base q hq hr 0 k hk a]
    rfl

theorem hillFullMixedComplexPeriodSequence_at_full_period_roots_eq_zero
    (N : ℕ) (hN : 1 ≤ N) (B D : ℝ) (hD : 0 ≤ D)
    (hc : HillComplexTailPeriodControl h0q h0r N B D)
    (hp : ‖SpectralWeight.one.toCoeff q‖ ≤ B) (a : Coeff 2)
    (hperiods : ∀ k : ℕ, 1 ≤ k → hillAbelianProductComplexPeriod q hq hr 0 k (a,SpectralWeight.one.toCoeff q)=0) :
    hillFullMixedComplexPeriodSequence q hq hr h0q h0r N (a,SpectralWeight.one.toCoeff q)=0 := by
  ext m
  change hillFullMixedComplexPeriodSequence q hq hr h0q h0r N (a,SpectralWeight.one.toCoeff q) m=0
  by_cases hm : m≤0
  · exact hillFullMixedComplexPeriodSequence_apply_nonpositive q hq hr h0q h0r N hN B D hD hc a _ hp m hm
  · have hcast : (m.toNat : ℤ)=m := by omega
    rw [←hcast,hillFullMixedComplexPeriodSequence_at_base_coordinate q hq hr h0q h0r N m.toNat hN (by omega) B D hD hc hp a,
      hperiods m.toNat (by omega),mul_zero]

end NLS.KdV
