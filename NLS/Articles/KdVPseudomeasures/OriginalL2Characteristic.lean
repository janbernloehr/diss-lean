import NLS.Articles.KdVPseudomeasures.OriginalHillSpectrum
import NLS.KdV.SingularHillL2Characteristic

/-! Physical L2 characteristic identification on the article's original
H-minus-one domain. Period-one parity is derived from the original potential. -/
noncomputable section
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue NLS.KdV

/-- Any L2 coefficient realization of an original physical potential has the
required even support; period one is not supplied as an extra hypothesis. -/
theorem originalL2_coefficients_mem_even (q : OriginalHminusOnePotential)
    (a : WeightedCoeff SpectralWeight.one.toWeight 2)
    (ha : ∀ k : ℤ, q.val.val (mode (-k)) = a.val k) :
    SpectralWeight.one.toCoeff a ∈ Coeff.paritySubspace 0 := by
  apply (Coeff.mem_paritySubspace 0 _).mpr
  intro k hk
  rw [SpectralWeight.toCoeff_apply]
  rw [← ha k]
  have hk' : k % 2 ≠ 0 := hk
  have he : k = 2*(k/2)+1 := by omega
  rw [he]
  exact (Distribution.toTempered_period_one_iff_odd q.val.val).mp q.property.2.2 (k/2)

/-- The ENTIRE original H1/H-minus-one spectrum of any original potential
with an L2 realization is detected by the ACTUAL physical L2 energy trace.
No simple-root, nonzero-energy or supplied eigenvector hypothesis is used. -/
theorem original_spectrum_iff_L2_discriminant (q : OriginalHminusOnePotential)
    (a : WeightedCoeff SpectralWeight.one.toWeight 2)
    (ha : ∀ k : ℤ, q.val.val (mode (-k)) = a.val k) (z : ℂ) :
    z ∈ singularHillSpectrum q.val ↔ hillL2Discriminant (SpectralWeight.one.toCoeff a) z ^ 2 = 4 := by
  have he : q.val = hillL2HminusOne a := by
    apply Subtype.ext
    apply Distribution.ext_coefficients
    intro k
    rw [hillL2HminusOne_coefficient, ha k]
  rw [he]
  exact singularHillSpectrum_L2_iff_discriminant a (originalL2_coefficients_mem_even q a ha) z

end NLS.Articles.KdVPseudomeasures
