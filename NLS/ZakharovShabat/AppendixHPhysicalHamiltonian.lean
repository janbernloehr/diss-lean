import NLS.ZakharovShabat.SobolevRiccatiClassicalAgreement
import NLS.Fourier.UnitIntervalL2Equiv

/-! # Appendix H's physical Hamiltonian integral at its original regularity

The coefficient-defined Hamiltonian is the literal unit-period integral
of the first field times the Riccati density on every complex H^(k-1)
source. Both factors have actual L2 representatives, so the formula
needs no additional smoothness or boundary matching.
-/
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace NLS.Fourier

/-- Bilinear Parseval for the actual synthesized unit-interval representatives. -/
theorem appendixH_unit_bilinear_parseval (a b : Coeff 2) :
    (∑' j : ℤ, a (-j)*b j) = ∫ x in (0 : ℝ)..1,
      unitL2SynthesisLinear a x*unitL2SynthesisLinear b x := by
  have h := tsum_bilinear_unitFourierCoefficient_of_memLp
    (Lp.memLp (unitL2SynthesisLinear a)) (Lp.memLp (unitL2SynthesisLinear b))
  have he (f : ℝ → ℂ) (j : ℤ) :
      unitFourierCoefficient f j = intervalFourierCoefficient 1 f j := by
    rw [unitFourierCoefficient_eq_fourierCoeffOn,
      intervalFourierCoefficient_eq_fourierCoeffOn (by norm_num : (0 : ℝ) < 1)]
  simpa only [he,unitL2SynthesisLinear_coefficient] using h

end NLS.Fourier

namespace NLS.ZakharovShabat
open NLS.Fourier

/-- The original normalized Hamiltonian is an actual physical integral on its full domain. -/
theorem appendixH_hamiltonian_eq_physical_integral
    (s n : ℕ) (hn : n ≤ s) (ab : SobolevSource s) :
    sobolevNLSHamiltonian s ab (n+1) (by omega) = (-Complex.I)^(n+2) *
      ∫ x in (0 : ℝ)..1,
        unitL2SynthesisLinear (WeightedCoeff.sobolevToL2 (Nat.cast_nonneg s) ab.1) x *
        unitL2SynthesisLinear (WeightedCoeff.sobolevToL2 (Nat.cast_nonneg (s-n))
          (sobolevRiccatiDensity s ab n hn)) x := by
  rw [sobolevNLSHamiltonian_succ_eq_tsum s n hn ab,
    ← appendixH_unit_bilinear_parseval]
  simp only [WeightedCoeff.sobolevToL2_apply]

/-- Every L2 representative with the original Fourier coefficients gives the same integral. -/
theorem appendixH_hamiltonian_eq_integral_of_coefficients
    (s n : ℕ) (hn : n ≤ s) (ab : SobolevSource s) (f u : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1)))
    (hu : MemLp u 2 (volume.restrict (Ioc 0 1)))
    (ha : ∀ j, periodOneCoefficient f j = ab.1.val j)
    (hd : ∀ j, periodOneCoefficient u j = (sobolevRiccatiDensity s ab n hn).val j) :
    sobolevNLSHamiltonian s ab (n+1) (by omega) =
      (-Complex.I)^(n+2) * ∫ x in (0 : ℝ)..1, f x*u x := by
  rw [sobolevNLSHamiltonian_succ_eq_tsum s n hn ab]
  congr 1
  have h := tsum_bilinear_unitFourierCoefficient_of_memLp hf hu
  have he (g : ℝ → ℂ) (j : ℤ) :
      unitFourierCoefficient g j = periodOneCoefficient g j :=
    unitFourierCoefficient_eq_fourierCoeffOn g j
  simpa only [he,ha,hd] using h

end NLS.ZakharovShabat
