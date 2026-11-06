import NLS.KdV.HillRoughActionApproximation
import NLS.KdV.HillOriginalActionFibers
import NLS.Articles.KdVKdV2Frequencies.GlobalRoughGroundEnergyFiniteGap

/-! # Full rough Hill discriminants on the actual positive action fibers -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.KdV
open NLS.Articles.KdVKdV2Frequencies

/-- Equal moduli of the actual positive coordinates determine the full
entire discriminant at all real mean-zero Hminus1 sources. No L2,
finite-gap, size or nonvanishing-action hypothesis remains. -/
theorem hillHminusDiscriminant_eq_of_positive_moduli
    (D : GlobalRoughAbelianForwardData) (q1 q2 : PeriodOneHminusOne)
    (hr1 : IsRealPeriodOneHminusOne q1) (hr2 : IsRealPeriodOneHminusOne q2)
    (hm1 : q1.val 0 = 0) (hm2 : q2.val 0 = 0)
    (he : ∀ n : ℕ+, ‖D.positive q1 (n : ℤ)‖ = ‖D.positive q2 (n : ℤ)‖) :
    hillHminusDiscriminant q1 = hillHminusDiscriminant q2 := by
  obtain ⟨p1,ht1,hs1⟩ := exists_physical_approximation_with_signed_truncations D q1 hr1 hm1
  obtain ⟨p2,ht2,hs2⟩ := exists_physical_approximation_with_signed_truncations D q2 hr2 hm2
  have hperiod : ∀ᶠ N : ℕ in atTop,
      hillHminusDiscriminant (hillOriginalHminusSource (p1 N).val.val) =
        hillHminusDiscriminant (hillOriginalHminusSource (p2 N).val.val) := by
    filter_upwards [hs1,hs2] with N hN1 hN2
    apply hillHminusDiscriminant_original_eq_of_actions
    intro n
    rw [D.positive_physical_action_norm ⟨(p1 N).val.val,(p1 N).val.property⟩ n n.pos,
      D.positive_physical_action_norm ⟨(p2 N).val.val,(p2 N).val.property⟩ n n.pos,
      positive_apply_of_signed_truncation D q1 _ hr1
        (hillOriginalHminusSource_real _ (p1 N).val.property.2) N hN1 n,
      positive_apply_of_signed_truncation D q2 _ hr2
        (hillOriginalHminusSource_real _ (p2 N).val.property.2) N hN2 n]
    split_ifs <;> simp only [he n]
  funext E
  have hlim1 := (analyticAt_hillHminusDiscriminant_source q1 E).continuousAt.tendsto.comp ht1
  have hlim2 := (analyticAt_hillHminusDiscriminant_source q2 E).continuousAt.tendsto.comp ht2
  exact tendsto_nhds_unique (hlim1.congr' (hperiod.mono fun _ hN => congrFun hN E)) hlim2

end NLS.KdV
