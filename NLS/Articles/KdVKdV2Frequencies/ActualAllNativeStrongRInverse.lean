import NLS.Articles.KdVKdV2Frequencies.ActualRoughInverseDomain
import NLS.Articles.KdVKdV2Frequencies.ActualNativeInverseMatching

/-! # ALL native inverse germs of the SAME retained R at every real base -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

/-- ONE common rough ball before ALL native orders and eligible real
mean-zero bases has genuine stronger analytic germs of the SAME actual R. -/
def HasAllNativeStrongRInverseGerms (η : ℝ)
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (W : Set (DeletedCoeff 2 0)) (R : DeletedCoeff 2 0 → PeriodOneHminusOne) : Prop :=
  ∃ ρ : ℝ, 0<ρ ∧ ρ≤η ∧ ∀ t : ℝ, ∀ ht : 0≤t, ∀ a : DeletedCoeff 2 0,
    IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion t ht
      (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1)) a)) →
    periodOneSobolevImageInclusion t ht (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1)) a)
      ∈ball (0 : PeriodOneHminusOne) ρ → NativeStrongRInverseAt η Z W R t ht a

/-- ANY GIVEN actual physical Z and retained weak right inverse R have
ALL genuine native analytic inverse germs at EVERY eligible real base
in ONE common rough ball. The full forward identity and both zero slots
are retained, and every stronger inverse agrees EXACTLY with THAT SAME R. -/
theorem exists_actual_all_native_strong_R_inverse_germs
    (η : ℝ) (hη : 0<η)
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (hZa : AnalyticOnNhd ℂ Z (ball (0 : PeriodOneHminusOne) η)) (hZ0 : Z 0=0)
    (hphys : ∀ p : RealPeriodOneHillPotential,
      (hillPhysicalHminusEmbedding p).val∈ball (0 : PeriodOneHminusOne) η → ∀ j : ℤ,
      (Z (hillPhysicalHminusEmbedding p).val).val j=
        hillAbelianRawCoordinateSequence SpectralWeight.one (hillUnitRealSourceUnembed p) j)
    (W : Set (DeletedCoeff 2 0)) (hW : IsOpen W) (h0W : (0 : DeletedCoeff 2 0)∈W)
    (R : DeletedCoeff 2 0 → PeriodOneHminusOne) (hRc : ContinuousOn R W) (hR0 : R 0=0)
    (hRdata : ∀ b∈W, (R b).val 0=0 ∧ Z (R b)=WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) b) :
    HasAllNativeStrongRInverseGerms η Z W R := by
  obtain ⟨δ,U,hδ,_hδη,hU,_h0U,_hUη,hi,hbase⟩ :=
    exists_actual_common_rough_inverse_domain η hη Z hZa hZ0 hphys W hW h0W R hRc hR0 hRdata
  obtain ⟨r,hr,hrη,hcharts⟩ := exists_actual_all_native_analytic_inverse_charts η hη Z hZa hphys
  let ρ := min δ r
  have hρ : 0<ρ := lt_min hδ hr
  refine ⟨ρ,hρ,(min_le_right _ _).trans hrη,?_⟩
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
    simpa only [mem_ball_zero_iff,L] using ball_subset_ball (min_le_left δ r) ha
  obtain ⟨haU,hbW,hRaU,_hRbase⟩ := hbase (J a) hJa
  exact nativeStrongRInverseAt_of_actual_chart η Z W hW R hRc hRdata U hU hi t ht a haU hbW hRaU
    (hcharts t ht a hreal (ball_subset_ball (min_le_right δ r) ha))

end NLS.Articles.KdVKdV2Frequencies
