import NLS.KdV.HillWeightedSpectralSequence
import NLS.SequenceSpaces.HilbertCoordinateNormContinuity

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

theorem continuous_hillWeightedSpectralCoordinate (w : SpectralWeight) (k : ℕ) :
    Continuous (fun p : RealHillWeightedPotential w => hillWeightedSpectralCoordinate w p k) := by
  have h := (continuous_hillSpectralCartesian h0q h0r (k+1) (by omega)).comp
    (continuous_hillRealWeightedEmbedding w)
  exact continuous_const.mul h

theorem norm_hillWeightedSpectralSequence
    (w : SpectralWeight) (p : RealHillWeightedPotential w) :
    ‖hillWeightedSpectralSequence h0q h0r w p‖ =
      Real.sqrt (2*∑' n : ℕ, hillWeightedActionTerm w p n) := by
  rw [← norm_hillWeightedSpectralSequence_sq h0q h0r w p,Real.sqrt_sq (norm_nonneg _)]

theorem continuous_norm_hillWeightedSpectralSequence (w : SpectralWeight) :
    Continuous (fun p : RealHillWeightedPotential w => ‖hillWeightedSpectralSequence h0q h0r w p‖) := by
  simp_rw [norm_hillWeightedSpectralSequence h0q h0r]
  exact Real.continuous_sqrt.comp (continuous_const.mul (continuous_tsum_hillWeightedActionTerm w))

theorem continuous_hillWeightedSpectralSequence (w : SpectralWeight) :
    Continuous (hillWeightedSpectralSequence h0q h0r w) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply NLS.SequenceSpaces.continuousAt_lp_two_of_coordinatewise_of_norm
  · intro k
    exact (continuous_hillWeightedSpectralCoordinate h0q h0r w k).continuousAt
  · exact (continuous_norm_hillWeightedSpectralSequence h0q h0r w).continuousAt

end NLS.KdV
