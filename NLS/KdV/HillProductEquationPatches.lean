import NLS.KdV.HillProductPlacementDomain
import NLS.KdV.HillPeriodSequenceMidpointFill

/-! Concrete native complex-source patches for the FULL Hill period
map. All analytic and geometric fields are supplied by a proved factory
near EVERY real source; the patch is independent of the numerator index. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

structure HillProductEquationPatch where
  parent : HillHminusPsiBall
  source : Set PeriodOneHminusOne
  source_open : IsOpen source
  subset : source ⊆ parent.source
  W : Set (CoeffPair 2)
  V : Set (CoeffPair 2)
  V_open : IsOpen V
  quotients : SourceCorollary10_6Data (by norm_num) (by norm_num) W
  discs : ℤ → Set ℂ
  separation : ℝ
  isolating : SourceIsolatingNeighborhoods (by norm_num) (by norm_num) V discs separation
  image : ∀ q ∈ source, hillMiuraDiagonal (parent.parent.miuraBall.actionBall.lift q) ∈ W ∩ V
  centers : ℤ → ℝ
  radii : ℤ → ℝ
  radii_pos : ∀ k : ℤ, 0 < radii k
  discs_eq : ∀ k : ℤ, discs k = ball (centers k:ℂ) (radii k)
  periods_analytic : ∀ (n : ℕ+) (k : ℤ), AnalyticOnNhd ℂ
    (parent.productPeriod n (centers k) (radii k)) (univ ×ˢ source)

theorem exists_hillProductEquationPatch (q₀ : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q₀) :
    ∃ P : HillProductEquationPatch, q₀ ∈ P.source ∧ P.parent.center = q₀ := by
  obtain ⟨A⟩ := nonempty_miuraHillPsiFamily
  obtain ⟨B,_,hB,hqB⟩ := exists_hillHminusPsiBall A q₀ hr
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
  exact ⟨P,⟨hqB,hTV,hRr hreal⟩,hB⟩

namespace HillProductEquationPatch

def sourcePsi (P : HillProductEquationPatch) (q : PeriodOneHminusOne) : CoeffPair 2 :=
  hillMiuraDiagonal (P.parent.parent.miuraBall.actionBall.lift q)

def inputDomain (P : HillProductEquationPatch) : Set (lp (fun _ : ℕ+ => ℂ) 2 × PeriodOneHminusOne) :=
  {t | ((P.parent.parent.miuraBall.actionBall.shift:ℂ),t.1) ∈ hillProductPlacementDomain P.discs ∧ t.2 ∈ P.source}

theorem inputDomain_open (P : HillProductEquationPatch) : IsOpen P.inputDomain :=
  ((isOpen_hillProductPlacementDomain P.isolating).preimage (continuous_const.prodMk continuous_fst)).inter
    (P.source_open.preimage continuous_snd)

theorem actual_real_graph_mem (P : HillProductEquationPatch) (q : PeriodOneHminusOne)
    (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q) ∈ P.inputDomain :=
  ⟨P.parent.actual_zero_data_mem_productPlacementDomain n q (P.subset hq) hr P.isolating (P.image q hq).2,hq⟩

theorem analytic_sourcePsi (P : HillProductEquationPatch) : AnalyticOnNhd ℂ P.sourcePsi P.source := by
  intro q hq
  exact (hillMiuraDiagonal.analyticAt _).comp
    (P.parent.parent.miuraBall.actionBall.lift_analytic q (P.parent.subset (P.subset hq)).1)

end HillProductEquationPatch
end NLS.KdV
