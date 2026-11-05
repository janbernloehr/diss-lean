import NLS.KdV.HillNativeAbelianScalarTransport
import NLS.KdV.HillUnitActionDirections
import NLS.SequenceSpaces.WeightedSignedModeGenerator

/-! # The actual native weighted Abelian derivative diagonalizes physical action directions -/
noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.KdV

private theorem zero_parity : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0 := by
  rw [map_zero]
  exact Submodule.zero_mem _
private theorem zero_real : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)) := by
  rw [map_zero]
  intro j
  simp

theorem fderiv_hillNativeAbelian_action_positive
    (η : ℝ) (Z : Coeff 2 → WeightedCoeff (hillAbelianTargetWeight SpectralWeight.one) 2)
    (hZa : AnalyticOnNhd ℂ Z (ball (0 : Coeff 2) η))
    (hphysical : ∀ p : RealHillWeightedPotential SpectralWeight.one,
      SpectralWeight.one.doubleIndex.toCoeff p.val ∈ ball (0 : Coeff 2) η →
      Z (SpectralWeight.one.doubleIndex.toCoeff p.val) = hillPhysicalAbelianMap SpectralWeight.one p)
    (p : RealHillWeightedPotential SpectralWeight.one)
    (hp : SpectralWeight.one.doubleIndex.toCoeff p.val ∈ ball (0 : Coeff 2) η)
    (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    ((fderiv ℂ Z (SpectralWeight.one.doubleIndex.toCoeff p.val)) (hillUnitActionDirection p m)).val (n : ℤ) =
      I*(if m=n then 1 else 0)*(Z (SpectralWeight.one.doubleIndex.toCoeff p.val)).val (n : ℤ) := by
  let q := hillRealWeightedEmbedding SpectralWeight.one p
  have hbase : Fourier.paritySample 0 (SpectralWeight.one.toCoeff q.val) =
      SpectralWeight.one.doubleIndex.toCoeff p.val := by
    rw [hillRealWeightedEmbedding_toCoeff,hillUnitSample_periodDouble]
  have hd := hasFDerivAt_hillNativeAbelianOriginalSection Z (n : ℤ)
    (SpectralWeight.one.toCoeff q.val) (by rw [hbase]; exact (hZa _ hp).differentiableAt)
  have hmatch := (hillNativeAbelianOriginalSection_eventually_physical η Z hphysical p hp (n : ℤ)).mono
    (fun s hs => hs.trans (hillPhysicalAbelianMap_unitUnembed_positive s n hn))
  have he := fderiv_hillDirichletAbelianCoordinate_extension_tracePeriodDirection q.val q.property.1 q.property.2
    zero_parity zero_real n m hn hm (hillNativeAbelianOriginalSection Z (n : ℤ)) hd.differentiableAt hmatch
  rw [hd.fderiv] at he
  change ((fderiv ℂ Z (Fourier.paritySample 0 (SpectralWeight.one.toCoeff q.val)))
    (hillUnitActionDirection p m)).val (n : ℤ) = _ at he
  rw [hbase] at he
  have hz : (Z (SpectralWeight.one.doubleIndex.toCoeff p.val)).val (n : ℤ) =
      hillDirichletAbelianCoordinate q.val q.property.1 q.property.2 n hn := by
    rw [hphysical p hp]
    exact hillPhysicalAbelianMap_positive p n hn
  rwa [hz]

theorem fderiv_hillNativeAbelian_action_negative
    (η : ℝ) (Z : Coeff 2 → WeightedCoeff (hillAbelianTargetWeight SpectralWeight.one) 2)
    (hZa : AnalyticOnNhd ℂ Z (ball (0 : Coeff 2) η))
    (hphysical : ∀ p : RealHillWeightedPotential SpectralWeight.one,
      SpectralWeight.one.doubleIndex.toCoeff p.val ∈ ball (0 : Coeff 2) η →
      Z (SpectralWeight.one.doubleIndex.toCoeff p.val) = hillPhysicalAbelianMap SpectralWeight.one p)
    (p : RealHillWeightedPotential SpectralWeight.one)
    (hp : SpectralWeight.one.doubleIndex.toCoeff p.val ∈ ball (0 : Coeff 2) η)
    (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    ((fderiv ℂ Z (SpectralWeight.one.doubleIndex.toCoeff p.val)) (hillUnitActionDirection p m)).val (-(n : ℤ)) =
      -I*(if m=n then 1 else 0)*(Z (SpectralWeight.one.doubleIndex.toCoeff p.val)).val (-(n : ℤ)) := by
  let q := hillRealWeightedEmbedding SpectralWeight.one p
  have hbase : Fourier.paritySample 0 (SpectralWeight.one.toCoeff q.val) =
      SpectralWeight.one.doubleIndex.toCoeff p.val := by
    rw [hillRealWeightedEmbedding_toCoeff,hillUnitSample_periodDouble]
  have hd := hasFDerivAt_hillNativeAbelianOriginalSection Z (-(n : ℤ))
    (SpectralWeight.one.toCoeff q.val) (by rw [hbase]; exact (hZa _ hp).differentiableAt)
  have hmatch := (hillNativeAbelianOriginalSection_eventually_physical η Z hphysical p hp (-(n : ℤ))).mono
    (fun s hs => hs.trans (hillPhysicalAbelianMap_unitUnembed_negative s n hn))
  have he := fderiv_hillNegativeAbelianCoordinate_extension_tracePeriodDirection q.val q.property.1 q.property.2
    zero_parity zero_real n m hn hm (hillNativeAbelianOriginalSection Z (-(n : ℤ))) hd.differentiableAt hmatch
  rw [hd.fderiv] at he
  change ((fderiv ℂ Z (Fourier.paritySample 0 (SpectralWeight.one.toCoeff q.val)))
    (hillUnitActionDirection p m)).val (-(n : ℤ)) = _ at he
  rw [hbase] at he
  have hz : (Z (SpectralWeight.one.doubleIndex.toCoeff p.val)).val (-(n : ℤ)) =
      (starRingEnd ℂ) (hillDirichletAbelianCoordinate q.val q.property.1 q.property.2 n hn) := by
    rw [hphysical p hp]
    exact hillPhysicalAbelianMap_negative p n hn
  rwa [hz]

end NLS.KdV
