import NLS.KdV.HillUnitRealSourceUnembed
import NLS.KdV.HillSignedAbelianHamiltonianVariation
import NLS.SequenceSpaces.WeightedFiniteCoefficients

/-! # Actual native scalar coordinates in the original physical source chart -/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ComplexConjugate
namespace NLS.KdV

theorem hillPhysicalAbelianMap_positive (p : RealHillWeightedPotential SpectralWeight.one)
    (n : ℕ) (hn : 1 ≤ n) :
    (hillPhysicalAbelianMap SpectralWeight.one p).val (n : ℤ) =
      let q := hillRealWeightedEmbedding SpectralWeight.one p
      hillDirichletAbelianCoordinate q.val q.property.1 q.property.2 n hn := by
  simp only [hillPhysicalAbelianMap,hillAbelianCoordinateSequence_apply,
    hillAbelianRawCoordinateSequence,Int.natCast_nonneg,if_true,Int.natAbs_natCast,
    hillAbelianPositiveCoefficient,dif_pos hn]

theorem hillPhysicalAbelianMap_negative (p : RealHillWeightedPotential SpectralWeight.one)
    (n : ℕ) (hn : 1 ≤ n) :
    (hillPhysicalAbelianMap SpectralWeight.one p).val (-(n : ℤ)) =
      let q := hillRealWeightedEmbedding SpectralWeight.one p
      conj (hillDirichletAbelianCoordinate q.val q.property.1 q.property.2 n hn) := by
  rw [(hillPhysicalAbelianMap_real SpectralWeight.one p).2,hillPhysicalAbelianMap_positive p n hn]

theorem hillPhysicalAbelianMap_unitUnembed_positive (p : RealPeriodOneHillPotential)
    (n : ℕ) (hn : 1 ≤ n) :
    (hillPhysicalAbelianMap SpectralWeight.one (hillUnitRealSourceUnembed p)).val (n : ℤ) =
      hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n hn := by
  simp only [hillPhysicalAbelianMap,hillAbelianCoordinateSequence_apply,
    hillAbelianRawCoordinateSequence,Int.natCast_nonneg,if_true,Int.natAbs_natCast,
    hillAbelianPositiveCoefficient,dif_pos hn,hillRealWeightedEmbedding_unitUnembed]

theorem hillPhysicalAbelianMap_unitUnembed_negative (p : RealPeriodOneHillPotential)
    (n : ℕ) (hn : 1 ≤ n) :
    (hillPhysicalAbelianMap SpectralWeight.one (hillUnitRealSourceUnembed p)).val (-(n : ℤ)) =
      conj (hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n hn) := by
  rw [(hillPhysicalAbelianMap_real SpectralWeight.one (hillUnitRealSourceUnembed p)).2,
    hillPhysicalAbelianMap_unitUnembed_positive p n hn]

def hillNativeAbelianOriginalSection
    (Z : Coeff 2 → WeightedCoeff (hillAbelianTargetWeight SpectralWeight.one) 2)
    (j : ℤ) (v : Coeff 2) : ℂ := (Z (Fourier.paritySample 0 v)).val j

theorem hasFDerivAt_hillNativeAbelianOriginalSection
    (Z : Coeff 2 → WeightedCoeff (hillAbelianTargetWeight SpectralWeight.one) 2)
    (j : ℤ) (v : Coeff 2) (hZ : DifferentiableAt ℂ Z (Fourier.paritySample 0 v)) :
    HasFDerivAt (hillNativeAbelianOriginalSection Z j)
      ((WeightedCoeff.evalCLM (hillAbelianTargetWeight SpectralWeight.one) 2 j).comp
        ((fderiv ℂ Z (Fourier.paritySample 0 v)).comp (Fourier.paritySample 0))) v := by
  exact (WeightedCoeff.evalCLM _ 2 j).hasFDerivAt.comp v
    (hZ.hasFDerivAt.comp v (Fourier.paritySample (p := 2) 0).hasFDerivAt)

theorem hillNativeAbelianOriginalSection_eventually_physical
    (η : ℝ)
    (Z : Coeff 2 → WeightedCoeff (hillAbelianTargetWeight SpectralWeight.one) 2)
    (hphysical : ∀ p : RealHillWeightedPotential SpectralWeight.one,
      SpectralWeight.one.doubleIndex.toCoeff p.val ∈ ball (0 : Coeff 2) η →
      Z (SpectralWeight.one.doubleIndex.toCoeff p.val) = hillPhysicalAbelianMap SpectralWeight.one p)
    (p : RealHillWeightedPotential SpectralWeight.one)
    (hp : SpectralWeight.one.doubleIndex.toCoeff p.val ∈ ball (0 : Coeff 2) η) (j : ℤ) :
    ∀ᶠ q : RealPeriodOneHillPotential in 𝓝 (hillRealWeightedEmbedding SpectralWeight.one p),
      hillNativeAbelianOriginalSection Z j (SpectralWeight.one.toCoeff q.val) =
        (hillPhysicalAbelianMap SpectralWeight.one (hillUnitRealSourceUnembed q)).val j := by
  have hc : Continuous (fun q : RealPeriodOneHillPotential =>
      Fourier.paritySample (p := 2) 0 (SpectralWeight.one.toCoeff q.val)) :=
    (Fourier.paritySample (p := 2) 0).continuous.comp
      (SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val)
  have hbase : Fourier.paritySample 0 (SpectralWeight.one.toCoeff
      (hillRealWeightedEmbedding SpectralWeight.one p).val) =
      SpectralWeight.one.doubleIndex.toCoeff p.val := by
    rw [hillRealWeightedEmbedding_toCoeff,hillUnitSample_periodDouble]
  have hnb := hc.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds (by rwa [hbase]))
  filter_upwards [hnb] with q hq
  have he := hphysical (hillUnitRealSourceUnembed q) (by
    rwa [hillUnitRealSourceUnembed_toCoeff])
  change (Z (Fourier.paritySample 0 (SpectralWeight.one.toCoeff q.val))).val j = _
  rw [← hillUnitRealSourceUnembed_toCoeff q,he]

end NLS.KdV
