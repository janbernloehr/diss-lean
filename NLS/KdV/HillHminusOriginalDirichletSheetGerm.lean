import NLS.KdV.HillHminusLogNorming
import NLS.KdV.HillHminusOriginalSheets
import NLS.KdV.HillDirichletSheetRoot

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.KdV

/-- The actual labelled Dirichlet sheet has an analytic H-minus-one
germ with its EXACT original physical sign, including collapsed gaps. -/
theorem exists_hillOriginal_dirichlet_sheet_hminus_physical_germ
    (q : RealPeriodOneHillPotential) (n : ℕ+) :
    ∃ a S : PeriodOneHminusOne → ℂ,
      AnalyticAt ℂ a (hillOriginalHminusSource q.val) ∧
      AnalyticAt ℂ S (hillOriginalHminusSource q.val) ∧
      a (hillOriginalHminusSource q.val) =
        (hillDirichletEnergy q.val q.property.1 q.property.2 n n.pos : ℂ) ∧
      (∀ᶠ b in 𝓝 (hillOriginalHminusSource q.val),
        S b^2 = hillHminusRadicand b (a b)) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        a (hillOriginalHminusSource p.val) =
          (hillDirichletEnergy p.val p.property.1 p.property.2 n n.pos : ℂ) ∧
        S (hillOriginalHminusSource p.val) = hillDirichletSheetRoot
          (SpectralWeight.one.toCoeff p.val) (hillDirichletEnergy p.val p.property.1 p.property.2 n n.pos) := by
  obtain ⟨a,T,k,ha,hT,_,ha0,_,_,hC,hM⟩ := exists_hillDirichlet_norming_hminus_analytic_extension q n n.pos
  let S : PeriodOneHminusOne → ℂ := fun b => 2*T b - hillHminusDiscriminant b (a b)
  have hD : AnalyticAt ℂ (fun b => hillHminusDiscriminant b (a b)) (hillOriginalHminusSource q.val) :=
    (analyticOnNhd_hillHminusDiscriminant_joint (a (hillOriginalHminusSource q.val),hillOriginalHminusSource q.val)
      (mem_univ _)).comp (f := fun b : PeriodOneHminusOne => (a b,b)) (ha.prod analyticAt_id)
  refine ⟨a,S,ha,(analyticAt_const.mul hT).sub hD,ha0,?_,?_⟩
  · filter_upwards [hC] with b hb
    dsimp only [S]
    unfold hillHminusRadicand
    rw [hb.2.2.2]
    field_simp [hb.2.1]
    ring
  · filter_upwards [hM] with p hp
    refine ⟨hp.1,?_⟩
    dsimp only [S]
    rw [hp.1,hp.2.1,hillHminusDiscriminant_original_source_agreement p.val p.property.1]
    rfl

end NLS.KdV
