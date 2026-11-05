import NLS.KdV.HillHminusClosedGapQuadraticChart
import NLS.KdV.HillHminusOriginalOwnGapFactor
import NLS.KdV.HillClosedGapAbelianCorrections
import NLS.KdV.HillGlobalRegularCorrection

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

/-- The exact ORIGINAL regular Abelian terminal correction has an analytic
H-minus-one germ through a collapsed selected gap. The mean subtraction
and the actual Dirichlet sheet, midpoint and terminal angle are retained. -/
theorem exists_hillOriginal_closedGap_regularCorrection_hminus_physical_germ
    (q : RealPeriodOneHillPotential) (n k : ℕ+)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 k = 0) :
    ∃ β : PeriodOneHminusOne → ℂ,
      AnalyticAt ℂ β (hillOriginalHminusSource q.val) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        β (hillOriginalHminusSource p.val) = hillRegularAbelianCorrection
          p.val p.property.1 p.property.2 n n.pos k k.pos := by
  have hc : hillRealLabels q.val q.property.1 q.property.2 (2*(k:ℕ)-1) =
      hillRealLabels q.val q.property.1 q.property.2 (2*(k:ℕ)) := by
    unfold hillRealGapHalfLength at hgap
    linarith
  obtain ⟨ρ,hρ,U,_,hqU,Q,hQ,hphysical⟩ := exists_hillHminusIntrinsicRegular_closed_gap_quadratic_chart
    q.val q.property.1 q.property.2 n k hc
  obtain ⟨μ,hμ,hμ0,_,hμM⟩ := exists_hillDirichletEnergy_hminus_analytic_extension q k k.pos
  obtain ⟨G,hG,hGM⟩ := exists_hillOriginal_ownGapFactor_hminus_physical_germ q k
  obtain ⟨A,_,hqA,hM,_,_⟩ := exists_hillHminusIntrinsicGapSymmetricData_analytic_neighborhood
    q.val q.property.1 q.property.2 k k.pos
  let τ := hillHminusIntrinsicGapMidpoint q.val q.property.1 q.property.2 k
  have hτ : AnalyticAt ℂ τ (hillOriginalHminusSource q.val) := hM _ hqA
  obtain ⟨W,hW,hqW,hdata⟩ := exists_hillHminusIntrinsicGapSymmetricData_physical_neighborhood
    q.val q.property.1 q.property.2 k k.pos
  have hτ0 := (hdata q hqW).1
  have hcenter : hillDirichletEnergy q.val q.property.1 q.property.2 k k.pos =
      hillRealGapCenter q.val q.property.1 q.property.2 k := by
    have hm := hillDirichletEnergy_mem_gap q.val q.property.1 q.property.2 k k.pos
    unfold hillRealGapCenter
    linarith [hm.1,hm.2]
  have hu0 : μ (hillOriginalHminusSource q.val)-τ (hillOriginalHminusSource q.val) = 0 := by
    dsimp only [τ]
    rw [hμ0,hτ0,hcenter,sub_self]
  have hQt : AnalyticAt ℂ (fun a : PeriodOneHminusOne => Q (μ a-τ a,a)) (hillOriginalHminusSource q.val) :=
    (hQ _ ⟨by rw [hu0]; exact mem_ball_self hρ,hqU⟩).comp
      (f := fun a : PeriodOneHminusOne => (μ a-τ a,a)) ((hμ.sub hτ).prod analyticAt_id)
  let β : PeriodOneHminusOne → ℂ := fun a => I*(G a-τ a+μ a)*Q (μ a-τ a,a)
  refine ⟨β,(analyticAt_const.mul ((hG.sub hτ).add hμ)).mul hQt,?_⟩
  filter_upwards [hphysical,hμM,hGM,hW.mem_nhds hqW] with p hp hμp hGp hpW
  have hβp : β (hillOriginalHminusSource p.val) =
      I*hillDirichletSheetRoot (SpectralWeight.one.toCoeff p.val)
        (hillDirichletEnergy p.val p.property.1 p.property.2 k k.pos) /
        hillDeflatedEnergyCanonicalRoot p.val p.property.1 p.property.2 k
          (hillDirichletEnergy p.val p.property.1 p.property.2 k k.pos) *
        Q ((hillDirichletEnergy p.val p.property.1 p.property.2 k k.pos : ℂ)-
          (hillRealGapCenter p.val p.property.1 p.property.2 k : ℂ),hillOriginalHminusSource p.val) := by
    dsimp only [β,τ]
    rw [hGp,(hdata p hpW).1,hμp,hillOwnGapFactor]
    ring
  rw [hβp]
  by_cases hpclosed : hillRealGapHalfLength p.val p.property.1 p.property.2 k = 0
  · rw [hillDirichletSheetRoot_eq_zero_of_halfLength_zero p.val p.property.1 p.property.2 k k.pos hpclosed,
      mul_zero,zero_div,zero_mul,hillRegularAbelianCorrection_closed p.val p.property.1 p.property.2 n n.pos k k.pos hpclosed]
  · have hspec := hillDirichletSelectedRealAngle_spec p.val p.property.1 p.property.2 k k.pos hpclosed
    rw [hillRegularAbelianCorrection,dif_neg hpclosed]
    have hQc : AnalyticOnNhd ℂ (fun w => Q (w,hillOriginalHminusSource p.val)) (ball (0:ℂ) ρ) := by
      intro w hw
      exact (hQ (w,hillOriginalHminusSource p.val) ⟨hw,hp.1⟩).comp
        (f := fun w : ℂ => (w,hillOriginalHminusSource p.val)) (analyticAt_id.prod analyticAt_const)
    exact hillRegularAbelian_terminal_eq_quadratic p.val p.property.1 p.property.2 n k n.pos k.pos hpclosed
      (fun w => Q (w,hillOriginalHminusSource p.val)) ρ hp.2.1 hQc
      (fun w hw => (hp.2.2 w hw).2) _ hspec.2.1 hspec.2.2

end NLS.KdV
