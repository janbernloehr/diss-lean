import NLS.Articles.KdVKdV2Frequencies.NativeRoughSobolevPositiveAbelian
import NLS.SequenceSpaces.SobolevSignedAnalyticGerms
import NLS.KdV.HillAbelianSignedPhysicalRecovery

/-! # The actual full signed rough Abelian map in every Sobolev topology

One map and common rough ball precede every Sobolev order and eligible
real source. Local complex signed completion retains the literal original
positive, negative and central coordinates, with exact native target
inclusion. The original physical recovery fixes the complete map.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

/-- ONE ACTUAL full signed rough Abelian map has genuine complex analytic
H^(t-1)-to-h^(t-1/2) germs at EVERY eligible real source, for ALL t>=0.
Original physical recovery, central zero and the real form are retained. -/
theorem exists_hillHminus_actual_all_sobolev_signed_abelian :
    ∃ η : ℝ, ∃ Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2,
      0<η ∧ AnalyticOnNhd ℂ Z (ball (0 : PeriodOneHminusOne) η) ∧ Z 0=0 ∧
      (∀ p : RealPeriodOneHillPotential,
        (hillPhysicalHminusEmbedding p).val∈ball (0 : PeriodOneHminusOne) η → ∀ j : ℤ,
        (Z (hillPhysicalHminusEmbedding p).val).val j=
          hillAbelianRawCoordinateSequence SpectralWeight.one (hillUnitRealSourceUnembed p) j) ∧
      (∀ q∈ball (0 : PeriodOneHminusOne) η, (Z q).val 0=0 ∧
        (IsRealPeriodOneHminusOne q → ∀ j : ℤ, (Z q).val (-j)=conj ((Z q).val j))) ∧
      ∀ t : ℝ, ∀ ht : 0≤t, ∀ q : WeightedCoeff (Weight.sobolev (t-1)) 2,
        IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion t ht q) →
        periodOneSobolevImageInclusion t ht q∈ball (0 : PeriodOneHminusOne) η →
        ∃ V : Set (WeightedCoeff (Weight.sobolev (t-1)) 2), IsOpen V ∧ q∈V ∧
          ∃ C : ℝ, ∃ g : WeightedCoeff (Weight.sobolev (t-1)) 2 → WeightedCoeff (Weight.sobolev (t-1/2)) 2,
            0≤C ∧ AnalyticOnNhd ℂ g V ∧ ∀ p∈V,
              periodOneSobolevImageInclusion t ht p∈ball (0 : PeriodOneHminusOne) η ∧ ‖g p‖≤C ∧
              WeightedCoeff.sobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2) (g p)=
                Z (periodOneSobolevImageInclusion t ht p) := by
  obtain ⟨η,C,P,hη,hC,hPa,hP0,hPb,hPphys,hstrong⟩ := exists_hillHminus_actual_all_sobolev_positive_abelian
  let v := Weight.sobolev (-1)
  let w := Weight.sobolev (-1/2)
  let Y := fun q => (WeightedCoeff.weightIsometry w 2).symm (P q)
  let Z := WeightedCoeff.signedTargetLift v w P
  have hYa : AnalyticOnNhd ℂ Y (ball (0 : PeriodOneHminusOne) η) := fun q hq =>
    ((WeightedCoeff.weightIsometry w 2).symm.toContinuousLinearEquiv.toContinuousLinearMap.analyticAt _).comp (hPa q hq)
  have hY0 : Y 0=0 := by simp only [Y,hP0,map_zero]
  have hYb (q : PeriodOneHminusOne) (hq : q∈ball (0 : PeriodOneHminusOne) η) :
      ‖Y q‖≤C*(‖q‖+‖q‖^2) := by
    rw [show ‖Y q‖=‖P q‖ from (WeightedCoeff.weightIsometry w 2).symm.norm_map _]
    exact (hPb q hq).1.trans (by nlinarith [sq_nonneg ‖q‖])
  obtain ⟨hSa,hS0,_hSb⟩ := WeightedCoeff.weightedSourceSignedCompletion_analytic_bound v w Y η C hYa hY0 hYb
  have hZeq : Z=WeightedCoeff.weightedSourceSignedCompletion v w Y := by
    funext q
    exact WeightedCoeff.signedTargetLift_eq_weightedSourceSignedCompletion v w P q
  have hcoord (q : PeriodOneHminusOne) (j : ℤ) :
      (Z q).val j=(Y q).val j+conj ((Y (periodOneHminusConjugation q)).val (-j)) := by
    rw [hZeq,WeightedCoeff.weightedSourceSignedCompletion_apply v w (Weight.sobolev_neg (-1)) (Weight.sobolev_neg (-1/2))]
    rfl
  have hnonpos (q : PeriodOneHminusOne) (hq : q∈ball (0 : PeriodOneHminusOne) η)
      (j : ℤ) (hj : j≤0) : (Y q).val j=0 := by
    change P q j/(w j : ℂ)=0
    rw [(hPb q hq).2 j hj,zero_div]
  refine ⟨η,Z,hη,?_,?_,?_,?_,?_⟩
  · rw [hZeq]
    exact hSa
  · rw [hZeq]
    exact hS0
  · intro p hp j
    exact hillAbelian_signedTargetLift_physical η P (fun q hq => (hPb q hq).2) hPphys p hp j
  · intro q hq
    have hJq : periodOneHminusConjugation q∈ball (0 : PeriodOneHminusOne) η := by
      simpa only [mem_ball_zero_iff,norm_periodOneHminusConjugation] using hq
    refine ⟨?_,?_⟩
    · rw [hcoord,hnonpos q hq 0 le_rfl,neg_zero,hnonpos _ hJq 0 le_rfl,map_zero,zero_add]
    · intro hr j
      have hJ : periodOneHminusConjugation q=q := (periodOneHminusConjugation_fixed_iff q).mpr hr
      rw [hcoord,hcoord,hJ,neg_neg,map_add,conj_conj]
      exact add_comm _ _
  · intro t ht q hr hq
    obtain ⟨U,hU,hqU,M,hM,hFa,hdata⟩ := hstrong t ht q hr hq
    exact exists_sobolev_signedTargetLift_germ t ht P η q hr U hU hqU M hM
      (Coeff.weightedSequenceRealization (fun n => (Weight.sobolev t n : ℂ))
        (fun p => P (periodOneSobolevImageInclusion t ht p))) hFa hdata

end NLS.Articles.KdVKdV2Frequencies
