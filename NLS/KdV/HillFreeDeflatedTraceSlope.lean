import NLS.KdV.HillFreeCoordinateNormalization

/-! # The exact free slope of the actual deflated Hill trace -/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem deriv_hillDeflatedTraceNumerator_free (n : ℕ) (hn : 1 ≤ n) :
    deriv (hillDeflatedTraceNumerator 0 h0q h0r n) (freeHillValue n) =
      I/(2*(n : ℂ)*Real.pi) := by
  have hc := neg_I_mul_deriv_hillDeflatedTraceNumerator_at_closed_gap 0 h0q h0r n hn
    ((hillFreeGapEndpoints h0q h0r n hn).1.trans (hillFreeGapEndpoints h0q h0r n hn).2.symm)
  rw [(hillFreeGapEndpoints h0q h0r n hn).1] at hc
  have hz : (freeHillValue n : ℂ) ∈ hillGapFilledDomain 0 h0q h0r n := by
    rw [←(hillFreeGapEndpoints h0q h0r n hn).1]
    exact hillGapSegment_subset_filledDomain 0 h0q h0r n hn (left_mem_segment ℝ _ _)
  rw [hillEnergyChi_free h0q h0r n _ hz,hillFreeGap_sqrt] at hc
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hp0 : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hn0,hp0] at hc ⊢
  linear_combination I*hc +
    (deriv (hillDeflatedTraceNumerator 0 h0q h0r n) (freeHillValue n)*(n : ℂ)*Real.pi*2)*I_sq

end NLS.KdV
