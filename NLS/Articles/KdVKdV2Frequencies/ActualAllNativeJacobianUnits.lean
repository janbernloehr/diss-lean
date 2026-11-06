import NLS.Articles.KdVKdV2Frequencies.ActualWeakJacobianNeighborhood

/-! # Actual native mean-zero Jacobian invertibility at EVERY eligible real base -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

/-- ONE smaller rough ball before ALL orders and real mean-zero bases
supports genuine native complex restrictions of the SAME actual map with
invertible literal mean-zero Jacobians at those bases. -/
def HasAllNativeJacobianUnits (η : ℝ)
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2) : Prop :=
  ∃ ρ : ℝ, 0<ρ ∧ ρ≤η ∧ ∀ t : ℝ, ∀ ht : 0≤t, ∀ a : DeletedCoeff 2 0,
    IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion t ht
      (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1)) a)) →
    periodOneSobolevImageInclusion t ht (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1)) a)
      ∈ball (0 : PeriodOneHminusOne) ρ →
    ∃ V : Set (WeightedCoeff (Weight.sobolev (t-1)) 2), IsOpen V ∧
      WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1)) a∈V ∧
      ∃ C : ℝ, ∃ g : WeightedCoeff (Weight.sobolev (t-1)) 2 → WeightedCoeff (Weight.sobolev (t-1/2)) 2,
        0≤C ∧ AnalyticOnNhd ℂ g V ∧
        (∀ p∈V, periodOneSobolevImageInclusion t ht p∈ball (0 : PeriodOneHminusOne) η ∧ ‖g p‖≤C ∧
          WeightedCoeff.sobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2) (g p)=Z (periodOneSobolevImageInclusion t ht p)) ∧
        IsUnit (fderiv ℂ (nativeMeanZeroAbelianMap t g) a)

/-- ANY GIVEN actual signed physical weak map has invertible native
mean-zero Jacobians at EVERY eligible real base in ONE common rough ball,
for ALL orders s>=-1. The actual strong germs and weak map are retained. -/
theorem exists_actual_all_native_jacobian_units
    (η : ℝ) (hη : 0<η)
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (hZa : AnalyticOnNhd ℂ Z (ball (0 : PeriodOneHminusOne) η))
    (hphys : ∀ p : RealPeriodOneHillPotential,
      (hillPhysicalHminusEmbedding p).val∈ball (0 : PeriodOneHminusOne) η → ∀ j : ℤ,
      (Z (hillPhysicalHminusEmbedding p).val).val j=
        hillAbelianRawCoordinateSequence SpectralWeight.one (hillUnitRealSourceUnembed p) j) :
    HasAllNativeJacobianUnits η Z := by
  obtain ⟨δ,hδ,_hδη,hweak⟩ := exists_actual_weak_jacobian_injective_ball η hη Z hZa hphys
  obtain ⟨r,hr,hrη,D,hrD,e,hstrong⟩ := exists_actual_signed_abelian_fourier_germs η hη Z hZa hphys
  let ρ := min δ r
  have hρ : 0<ρ := lt_min hδ hr
  have hρr : ρ≤r := min_le_right _ _
  have hρδ : ρ≤δ := min_le_left _ _
  refine ⟨ρ,hρ,hρr.trans hrη,?_⟩
  intro t ht a hreal ha
  let L := WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1))
  let J := WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1 : ℝ)≤t-1)
  have hsource : WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1)) (J a)=
      periodOneSobolevImageInclusion t ht (L a) :=
    WeightedCoeff.meanZeroSobolevInclusion_lift _ a
  have hnorm : ‖J a‖=‖periodOneSobolevImageInclusion t ht (L a)‖ := by
    rw [←hsource,WeightedCoeff.meanZeroWeightedLift_norm]
  have hJa : J a∈ball (0 : DeletedCoeff 2 0) δ := by
    rw [mem_ball_zero_iff,hnorm]
    simpa only [mem_ball_zero_iff,L] using ball_subset_ball hρδ ha
  have haR : periodOneSobolevImageInclusion t ht (L a)∈ball (0 : PeriodOneHminusOne) r :=
    ball_subset_ball hρr ha
  obtain ⟨V,hV,haV,_hJ,C,g,hC,hga,hgd⟩ := hstrong t ht (L a) hreal haR
  have hu := isUnit_fderiv_nativeMeanZero_of_actual_weak_injective D e t ht Z V hV g hga
    (fun p hp => (hgd p hp).2.2.1) a haV (ball_subset_ball hrD haR) hreal
    ((hgd (L a) haV).2.2.2 hreal) (hweak (J a) hJa).2.1 (hweak (J a) hJa).2.2
  exact ⟨V,hV,haV,C,g,hC,hga,fun p hp =>
    ⟨ball_subset_ball hrη (hgd p hp).1,(hgd p hp).2.1,(hgd p hp).2.2.1⟩,hu⟩

end NLS.Articles.KdVKdV2Frequencies
