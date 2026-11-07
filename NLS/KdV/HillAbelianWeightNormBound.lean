import NLS.KdV.HillAbelianUniformValueTail
import NLS.ZakharovShabat.SourcePeriodicGapTails

/-! Locally bounded full-l2 weights for ACTUAL Hill Abelian sums.
The Dirichlet weight uses the AUXILIARY frequency displacement. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

def physicalAbelianMidpointDisplacement (P : HillProductEquationPatch) (q : PeriodOneHminusOne) : Coeff 2 :=
  hillMiuraDirichletDisplacement (P.parent.parent.miuraBall.actionBall.lift q)-
    sourcePeriodicMidpointDisplacement (by norm_num) (by norm_num) (P.sourcePsi q)

theorem physicalAbelianMidpointDisplacement_apply (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (m : ℤ) :
    P.physicalAbelianMidpointDisplacement q m = P.physicalDirichletFrequency m q-
      sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) m := by
  simp only [physicalAbelianMidpointDisplacement,lp.coeFn_sub,Pi.sub_apply,
    hillMiuraDirichletDisplacement_apply,sourcePeriodicMidpointDisplacement_apply,
    sourceStandardRootMidpoint,physicalDirichletFrequency]
  ring

theorem exists_local_abelianWeight_norm_bound (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧ U ⊆ P.source ∧
      ∃ R : ℝ, 0 < R ∧ ∀ a ∈ U,
        ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi a)‖+
          ‖P.physicalAbelianMidpointDisplacement a‖ ≤ R := by
  obtain ⟨_,_,G,hG,hqG,Rg,hRg,hgap⟩ := exists_uniform_small_sourcePeriodicGapDisplacement
    (by norm_num) (by norm_num) (P.sourcePsi q) (by norm_num : (0:ℝ) < 1)
  obtain ⟨_,_,M,hM,hqM,Rm,hRm,hmid⟩ := exists_uniform_small_sourcePeriodicMidpointDisplacement
    (by norm_num) (by norm_num) (P.sourcePsi q) (by norm_num : (0:ℝ) < 1)
  let μ : PeriodOneHminusOne → Coeff 2 := fun a => hillMiuraDirichletDisplacement (P.parent.parent.miuraBall.actionBall.lift a)
  have hμ : AnalyticAt ℂ μ q := P.parent.parent.analytic_auxiliaryDisplacement q (P.parent.subset (P.subset hq)).1
  have hnear : ∀ᶠ a in 𝓝 q, ‖μ a‖ < ‖μ q‖+1 :=
    hμ.continuousAt.norm.eventually (Iio_mem_nhds (by linarith))
  obtain ⟨B,hBsub,hB,hqB⟩ := _root_.mem_nhds_iff.mp hnear
  let V := P.source ∩ P.sourcePsi ⁻¹' (G ∩ M)
  have hV : IsOpen V := P.analytic_sourcePsi.continuousOn.isOpen_inter_preimage P.source_open (hG.inter hM)
  refine ⟨V ∩ B,hV.inter hB,⟨⟨hq,hqG,hqM⟩,hqB⟩,(fun a ha => ha.1.1),
    Rg+‖μ q‖+1+Rm,by positivity,?_⟩
  intro a ha
  have hg := (hgap (P.sourcePsi a) ha.1.2.1).1
  have hm := (hmid (P.sourcePsi a) ha.1.2.2).1
  have hb : ‖μ a‖ ≤ ‖μ q‖+1 := (show ‖μ a‖ < ‖μ q‖+1 from hBsub ha.2).le
  have hd : ‖P.physicalAbelianMidpointDisplacement a‖ ≤
      ‖μ a‖+‖sourcePeriodicMidpointDisplacement (by norm_num) (by norm_num) (P.sourcePsi a)‖ :=
    norm_sub_le _ _
  linarith

end NLS.KdV.HillProductEquationPatch
