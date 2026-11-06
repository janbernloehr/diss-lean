import NLS.SequenceSpaces.PeriodOneRealFormIdentityAt
import NLS.KdV.HillHminusOriginalSourceAdapter
import NLS.KdV.HillUnitRealSourceUnembed

/-! # Original physical values determine rough maps away from zero

Real L2 density first gives equality on the full rough real slice.
The actual real-form identity then determines the native complex map
on any connected open domain with a real point, including chart overlaps.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.KdV

def hillPhysicalRealL2Lift (a : PeriodOneRealL2) : RealPeriodOneHillPotential :=
  hillRealWeightedEmbedding SpectralWeight.one (hillUnitRealSourceLift a.val
    ((periodOneL2Conjugation_fixed_iff _).mpr a.property))

theorem hillPhysicalRealL2Lift_hminus (a : PeriodOneRealL2) :
    (hillPhysicalHminusEmbedding (hillPhysicalRealL2Lift a)).val =
      (periodOneRealL2Inclusion a).val := by
  change periodOneL2Inclusion (Fourier.paritySample 0
    (SpectralWeight.one.toCoeff (hillPhysicalRealL2Lift a).val)) = periodOneL2Inclusion a.val
  unfold hillPhysicalRealL2Lift
  rw [hillRealWeightedEmbedding_toCoeff,hillUnitRealSourceLift_toCoeff,hillUnitSample_periodDouble]

theorem eqOn_real_rough_of_physical_eq
    {Y : Type*} [NormedAddCommGroup Y] (U : Set PeriodOneHminusOne) (hU : IsOpen U)
    (F G : PeriodOneHminusOne → Y) (hF : ContinuousOn F U) (hG : ContinuousOn G U)
    (he : ∀ p : RealPeriodOneHillPotential, (hillPhysicalHminusEmbedding p).val ∈ U →
      F (hillPhysicalHminusEmbedding p).val = G (hillPhysicalHminusEmbedding p).val) :
    ∀ q ∈ U, IsRealPeriodOneHminusOne q → F q = G q := by
  let V : Set PeriodOneRealHminusOne := Subtype.val ⁻¹' U
  have hV : IsOpen V := hU.preimage continuous_subtype_val
  have hFc : ContinuousOn (fun q : PeriodOneRealHminusOne => F q.val) V :=
    hF.comp continuous_subtype_val.continuousOn (fun _ h => h)
  have hGc : ContinuousOn (fun q : PeriodOneRealHminusOne => G q.val) V :=
    hG.comp continuous_subtype_val.continuousOn (fun _ h => h)
  have hEq : EqOn (fun q : PeriodOneRealHminusOne => F q.val) (fun q => G q.val)
      (V ∩ range periodOneRealL2Inclusion) := by
    rintro _ ⟨hq,a,rfl⟩
    have hp : (hillPhysicalHminusEmbedding (hillPhysicalRealL2Lift a)).val ∈ U := by
      rw [hillPhysicalRealL2Lift_hminus]
      exact hq
    simpa only [hillPhysicalRealL2Lift_hminus] using he (hillPhysicalRealL2Lift a) hp
  have hfull : EqOn (fun q : PeriodOneRealHminusOne => F q.val) (fun q => G q.val) V :=
    hEq.of_subset_closure hFc hGc inter_subset_left
      (fun q hq => hV.inter_closure ⟨hq,denseRange_periodOneRealL2Inclusion q⟩)
  intro q hq hr
  exact hfull (show (⟨q,hr⟩ : PeriodOneRealHminusOne) ∈ V from hq)

theorem eqOn_rough_domain_of_physical_eq
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    (U : Set PeriodOneHminusOne) (hU : IsOpen U) (hconn : IsPreconnected U)
    (q0 : PeriodOneHminusOne) (hq0 : q0 ∈ U) (hr0 : IsRealPeriodOneHminusOne q0)
    (F G : PeriodOneHminusOne → Y) (hF : AnalyticOnNhd ℂ F U) (hG : AnalyticOnNhd ℂ G U)
    (he : ∀ p : RealPeriodOneHillPotential, (hillPhysicalHminusEmbedding p).val ∈ U →
      F (hillPhysicalHminusEmbedding p).val = G (hillPhysicalHminusEmbedding p).val) : EqOn F G U := by
  exact periodOneHminus_real_form_identity_at hU hconn q0 hq0 hr0 F G hF hG
    (eqOn_real_rough_of_physical_eq U hU F G hF.continuousOn hG.continuousOn he)

theorem eqOn_rough_real_centered_ball_inter_of_physical_eq
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    (q0 q1 : PeriodOneHminusOne) (hr0 : IsRealPeriodOneHminusOne q0)
    (hr1 : IsRealPeriodOneHminusOne q1) (r s : ℝ)
    (F G : PeriodOneHminusOne → Y) (hF : AnalyticOnNhd ℂ F (ball q0 r))
    (hG : AnalyticOnNhd ℂ G (ball q1 s))
    (he : ∀ p : RealPeriodOneHillPotential,
      (hillPhysicalHminusEmbedding p).val ∈ ball q0 r ∩ ball q1 s →
        F (hillPhysicalHminusEmbedding p).val = G (hillPhysicalHminusEmbedding p).val) :
    EqOn F G (ball q0 r ∩ ball q1 s) := by
  by_cases hne : (ball q0 r ∩ ball q1 s).Nonempty
  · obtain ⟨q,hq,hr⟩ := real_point_of_inter_real_centered_rough_balls q0 q1 hr0 hr1 r s hne
    exact eqOn_rough_domain_of_physical_eq _ (isOpen_ball.inter isOpen_ball)
      ((convex_ball q0 r).inter (convex_ball q1 s)).isPreconnected q hq hr F G
      (hF.mono inter_subset_left) (hG.mono inter_subset_right) he
  · intro q hq
    exact (hne ⟨q,hq⟩).elim

end NLS.KdV
