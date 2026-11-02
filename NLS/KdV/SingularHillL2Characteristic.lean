import NLS.KdV.SingularHillL2Domain
import NLS.KdV.HillL2EnergyDiscriminant

/-! The actual original full-domain H-minus-one spectrum at L2 potentials
is detected by the independently verified physical monodromy discriminant. -/
noncomputable section
namespace NLS.KdV

/-- The actual original H1/H-minus-one spectrum at every complex period-one
L2 potential is EXACTLY the physical energy characteristic zero set. -/
theorem singularHillSpectrum_L2_iff_discriminant
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0) (z : ℂ) :
    z ∈ singularHillSpectrum (hillL2HminusOne q) ↔
      hillL2Discriminant (SpectralWeight.one.toCoeff q) z ^ 2 = 4 := by
  rw [mem_singularHillSpectrum_iff, singularHillL2_exists_eigenvector_iff]
  exact hill_eigenvector_iff_l2Discriminant q hq z

/-- The same exact original spectral criterion in the frequency variable,
with energy z squared and no division by z, including zero energy. -/
theorem singularHillSpectrum_L2_iff_frequencyDiscriminant
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0) (z : ℂ) :
    z^2 ∈ singularHillSpectrum (hillL2HminusOne q) ↔
      hillL2FrequencyDiscriminant (SpectralWeight.one.toCoeff q) z ^ 2 = 4 := by
  rw [singularHillSpectrum_L2_iff_discriminant q hq, hillL2Discriminant_sq]

end NLS.KdV
