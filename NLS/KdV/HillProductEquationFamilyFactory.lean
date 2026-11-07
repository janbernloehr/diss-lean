import NLS.KdV.HillProductEquationPatches

/-! Native original product patches for ANY supplied verified Hill family. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

theorem exists_hillProductEquationPatch_with_family (A : MiuraHillPsiFamily) (q₀ : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q₀) :
    ∃ P : HillProductEquationPatch, q₀ ∈ P.source ∧ P.parent.center = q₀ ∧ P.parent.family = A := by
  obtain ⟨B,hBA,hB,hqB⟩ := exists_hillHminusPsiBall A q₀ hr
  let T : PeriodOneHminusOne → CoeffPair 2 := fun q => hillMiuraDiagonal (B.parent.miuraBall.actionBall.lift q)
  let u : PeriodOneRealL2 := ⟨B.parent.miuraBall.actionBall.lift q₀,
    B.parent.miuraBall.actionBall.lift_real q₀ (B.subset hqB).1 hr⟩
  have hreal : IsRealType (CoeffPair.toMax 2 (T q₀)) := (hillMiuraRealSource u).property
  obtain ⟨Wr,hWr,_,hRr,hDom,hRoot⟩ := exists_global_source_analytic_canonicalRoot (p := 2) (by norm_num) (by norm_num)
  obtain ⟨W,_,_,hRW,H⟩ := sourceCorollary10_6 (p := 2) (by norm_num) (by norm_num)
  obtain ⟨V,hV,_,hTV,hVW,D,C,hD⟩ := H.neighborhoods (T q₀) (hRW hreal)
  choose a R hR he using hD.discs
  have hT : AnalyticOnNhd ℂ T B.source := by
    intro q hq
    exact (hillMiuraDiagonal.analyticAt _).comp (B.parent.miuraBall.actionBall.lift_analytic q (B.subset hq).1)
  let U := B.source ∩ T ⁻¹' (V ∩ Wr)
  have hU : IsOpen U := hT.continuousOn.isOpen_inter_preimage B.source_open (hV.inter hWr)
  let P : HillProductEquationPatch := {
    parent := B
    source := U
    source_open := hU
    subset := inter_subset_left
    W := W
    V := V
    V_open := hV
    quotients := H
    discs := D
    separation := C
    isolating := hD.toSourceIsolatingNeighborhoods
    image := fun q hq => ⟨hVW hq.2.1,hq.2.1⟩
    centers := a
    radii := R
    radii_pos := hR
    discs_eq := he
    periods_analytic := by
      intro n k
      apply B.analytic_productPeriod n (a k) (R k) (V ∩ Wr) _ U inter_subset_left (fun _ hq => hq.2)
      apply analyticOnNhd_hillEnergyProductJointPeriod Wr (V ∩ Wr) hDom hRoot (hV.inter hWr)
        inter_subset_right (a k:ℂ) (R k) (hR k).le _ n
      intro ψ hψ
      exact (hD.toSourceIsolatingNeighborhoods.periodCircle ψ hψ.1 k (a k) (R k) (hR k) (he k)).sphere_subset_rootDomain }
  exact ⟨P,⟨hqB,hTV,hRr hreal⟩,hB,hBA⟩

end NLS.KdV
