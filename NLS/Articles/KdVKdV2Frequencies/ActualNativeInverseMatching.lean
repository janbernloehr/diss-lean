import NLS.Articles.KdVKdV2Frequencies.ActualNativeAnalyticInverseCharts
import NLS.Articles.KdVKdV2Frequencies.NativeAbelianInverseRecovery
import NLS.ComplexAnalysis.LocalRightInverseMatchingAt

/-! # Strong inverse germs of the SAME actual rough inverse at real bases -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

/-- A genuine native analytic germ of the GIVEN rough inverse R around
the ACTUAL native image of a base. All raw coefficients, source and
target zero slots, the actual weak inclusion and full right inverse hold. -/
def NativeStrongRInverseAt (η : ℝ)
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (W : Set (DeletedCoeff 2 0)) (R : DeletedCoeff 2 0 → PeriodOneHminusOne)
    (t : ℝ) (ht : 0≤t) (a : DeletedCoeff 2 0) : Prop :=
  ∃ V : Set (WeightedCoeff (Weight.sobolev (t-1)) 2), IsOpen V ∧
    WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1)) a∈V ∧
    ∃ g : WeightedCoeff (Weight.sobolev (t-1)) 2 → WeightedCoeff (Weight.sobolev (t-1/2)) 2,
      AnalyticOnNhd ℂ g V ∧
      (∀ p∈V, periodOneSobolevImageInclusion t ht p∈ball (0 : PeriodOneHminusOne) η ∧
        WeightedCoeff.sobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2) (g p)=Z (periodOneSobolevImageInclusion t ht p)) ∧
      ∃ T : Set (DeletedCoeff 2 0), IsOpen T ∧ nativeMeanZeroAbelianMap t g a∈T ∧
        ∃ G : DeletedCoeff 2 0 → WeightedCoeff (Weight.sobolev (t-1)) 2,
          AnalyticOnNhd ℂ G T ∧
          G (nativeMeanZeroAbelianMap t g a)=WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1)) a ∧
          ∀ b∈T, WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2) b∈W ∧
            G b∈V ∧ (G b).val 0=0 ∧
            periodOneSobolevImageInclusion t ht (G b)=
              R (WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2) b) ∧
            g (G b)=WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1/2)) b

/-- Actual native inverse charts match the GIVEN R at ANY base whose two
actual weak sources lie in the common injectivity domain. The full native
right-inverse identity, including the target zero slot, is recovered. -/
theorem nativeStrongRInverseAt_of_actual_chart
    (η : ℝ) (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (W : Set (DeletedCoeff 2 0)) (hW : IsOpen W)
    (R : DeletedCoeff 2 0 → PeriodOneHminusOne) (hRc : ContinuousOn R W)
    (hRdata : ∀ b∈W, (R b).val 0=0 ∧ Z (R b)=WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) b)
    (U : Set (DeletedCoeff 2 0)) (hU : IsOpen U) (hi : InjOn (weakMeanZeroAbelianMap Z) U)
    (t : ℝ) (ht : 0≤t) (a : DeletedCoeff 2 0)
    (haU : WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1 : ℝ)≤t-1) a∈U)
    (hbW : weakMeanZeroAbelianMap Z (WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1 : ℝ)≤t-1) a)∈W)
    (hRaU : WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1))
      (R (weakMeanZeroAbelianMap Z (WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1 : ℝ)≤t-1) a)))∈U)
    (hchart : NativeAbelianAnalyticInverseAt η Z t ht a) :
    NativeStrongRInverseAt η Z W R t ht a := by
  obtain ⟨V,hV,haV,g,hga,hcomm,P,hP,haP,hPV,_hFa,hPia⟩ := hchart
  let L := WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1))
  let J := WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1 : ℝ)≤t-1)
  let I := WeightedCoeff.meanZeroSobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2)
  let L0 := WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1))
  let P0 := WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1))
  let Q0 := WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1/2))
  let R0 := fun b => P0 (R b)
  have hRc0 : ContinuousOn R0 W := P0.continuous.comp_continuousOn hRc
  have hsolve (b : DeletedCoeff 2 0) (hb : b∈W) : weakMeanZeroAbelianMap Z (R0 b)=b := by
    change Q0 (Z (L0 (P0 (R b))))=b
    rw [WeightedCoeff.meanZeroWeightedLift_projection _ _ (hRdata b hb).1,(hRdata b hb).2]
    exact WeightedCoeff.meanZeroWeightedProjection_lift _ b
  have hPa : nativeMeanZeroAbelianMap t g a=P a := (congrFun hP a).symm
  have hIcenter : I (P a)=weakMeanZeroAbelianMap Z (J a) := by
    have h := nativeMeanZeroAbelianMap_commuting t ht Z g a (hcomm (L a) haV).2
    rw [hPa] at h
    exact h
  have hgsolve (b : DeletedCoeff 2 0) (hb : b∈P.target) :
      weakMeanZeroAbelianMap Z (J (P.symm b))=I b := by
    have h := nativeMeanZeroAbelianMap_commuting t ht Z g (P.symm b)
      (hcomm _ (hPV (P.map_target hb))).2
    have he : nativeMeanZeroAbelianMap t g (P.symm b)=b :=
      (congrFun hP (P.symm b)).symm.trans (P.right_inv hb)
    rw [he] at h
    exact h.symm
  obtain ⟨T,hT,hbT,hTP,hPiaT,hmatch⟩ := NLS.ComplexAnalysis.exists_local_rightInverse_matching_at
    J I (weakMeanZeroAbelianMap Z) U hU hi W hW R0 hRc0 hsolve
    P.target P.open_target P.symm hPia hgsolve (P a) (P.map_source haP)
    (by rw [hIcenter];exact hbW) (by rw [P.left_inv haP];exact haU) (by rw [hIcenter];exact hRaU)
  let G := fun b => L (P.symm b)
  refine ⟨V,hV,haV,g,hga,hcomm,T,hT,?_,G,?_,?_,?_⟩
  · rw [hPa]
    exact hbT
  · intro b hb
    exact (L.analyticAt _).comp (hPiaT b hb)
  · change L (P.symm (nativeMeanZeroAbelianMap t g a))=L a
    rw [hPa,P.left_inv haP]
  · intro b hb
    have hbW' := (hmatch b hb).1
    have hbV := hPV (P.map_target (hTP hb))
    have hs := native_source_lift_recovery t ht (P.symm b) (I b) R (hRdata _ hbW').1 (hmatch b hb).2
    refine ⟨hbW',hbV,WeightedCoeff.meanZeroWeightedLift_zero _ _,hs,?_⟩
    apply native_inverse_full_target_recovery t ht Z g R (P.symm b) b (hcomm _ hbV).2 hs (hRdata _ hbW').2
    exact (congrFun hP (P.symm b)).symm.trans (P.right_inv (hTP hb))

end NLS.Articles.KdVKdV2Frequencies
