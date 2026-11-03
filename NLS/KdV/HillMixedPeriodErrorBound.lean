import NLS.KdV.HillMixedPhysicalPeriodCoordinates

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

theorem hillMixedComplexPeriodSequence_high_coordinate
    (N n : ℕ) (hn : 1 ≤ n) (t : Coeff 2 × Coeff 2) (m : ℤ) (hm : N ≤ m.natAbs) :
    hillMixedComplexPeriodSequence q hq hr h0q h0r N n t m =
      hillComplexScaledPeriodCoordinate h0q h0r n t m := by
  by_cases hpos : 0 < m ∧ m ≠ (n : ℤ)
  · have hk : 1 ≤ m.toNat := by omega
    have hkn : m.toNat ≠ n := by omega
    have hcast : (m.toNat : ℤ) = m := by omega
    have hkN : ¬m.toNat < N := by omega
    rw [← hcast,hillMixedComplexPeriodSequence_apply_nat q hq hr h0q h0r N n m.toNat hn hk,
      if_pos hkn,if_neg hkN]
    simp only [hillComplexScaledPeriodCoordinate,Int.toNat_natCast]
    rw [if_pos (show (0 : ℤ) < (m.toNat : ℤ) ∧ (m.toNat : ℤ) ≠ n by omega)]
  · rw [hillMixedComplexPeriodSequence_apply_unsupported q hq hr h0q h0r N n hn t m (by omega),
      hillComplexScaledPeriodCoordinate,if_neg hpos]

theorem norm_hillMixedComplexPeriodSequence_sub_free_high_coordinate_le
    (N n : ℕ) (hn : 1 ≤ n) (B D : ℝ) (hD : 0 ≤ D)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) (a p : Coeff 2) (hp : ‖p‖ ≤ B)
    (m : ℤ) (hm : N ≤ m.natAbs) :
    ‖(hillMixedComplexPeriodSequence q hq hr h0q h0r N n (a,p)-
      hillFreeScaledPeriodSequence h0q h0r n hn a) m‖ ≤
        (D*Real.exp ((8/Real.pi^2)*‖a‖)*‖p‖)*‖Coeff.positivePuncturedLattice 2 (by norm_num) m‖ := by
  rw [lp.coeFn_sub,Pi.sub_apply,hillMixedComplexPeriodSequence_high_coordinate q hq hr h0q h0r N n hn _ m hm,
    hillFreeScaledPeriodSequence_apply]
  exact norm_hillComplexScaledPeriodCoordinate_sub_free_le_on_tail h0q h0r N n a p D hD
    (fun k hk hnk => (hc p hp).2 n k hn hk hnk a) m hm

end NLS.KdV
