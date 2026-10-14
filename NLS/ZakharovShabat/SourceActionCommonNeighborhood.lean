import NLS.ZakharovShabat.SourceBirkhoffMapAnalytic
import NLS.ZakharovShabat.SourceComplexActionProperties

/-!
# A common analytic neighborhood for every scalar action

The actual rectangular sequence map gives all action coordinates on one
open neighborhood of the whole real locus. Scalar coordinate evaluation
works for every finite p>1, including the range below two.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- All indexed actions are analytic on the same Birkhoff neighborhood. -/
theorem SourceBirkhoffMapComplexData.actions_analytic
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
    {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (n : ℤ) :
    AnalyticOnNhd ℂ (sourceComplexAction hp hp1 n) W := by
  intro φ hφ
  let ev := lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n
  have hx : AnalyticAt ℂ (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).1 n) φ :=
    (ev.analyticAt _).comp (analyticAt_fst.comp (D.analytic φ hφ))
  have hy : AnalyticAt ℂ (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).2 n) φ :=
    (ev.analyticAt _).comp (analyticAt_snd.comp (D.analytic φ hφ))
  have ha := ((hx.pow 2).add (hy.pow 2)).div analyticAt_const (by norm_num : (2 : ℂ) ≠ 0)
  apply ha.congr
  filter_upwards [D.source_open.mem_nhds hφ] with ψ hψ
  change (((sourceBirkhoffMap hp hp1 s ψ).1 n)^2 + ((sourceBirkhoffMap hp hp1 s ψ).2 n)^2)/2 = _
  rw [D.action_radius ψ hψ n]
  ring

/-- Theorem 7.1(i): one original neighborhood serves every action and every finite p>1. -/
theorem exists_sourceAction_common_analytic_neighborhood (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ n : ℤ, AnalyticOnNhd ℂ (sourceComplexAction hp hp1 n) W ∧
        AnalyticOnNhd ℝ (sourceComplexAction hp hp1 n) W := by
  obtain ⟨W₀,B,W,s,D⟩ := exists_sourceBirkhoffMap_complex_analytic hp hp1
  exact ⟨W,D.source_open,D.real_subset,fun n =>
    ⟨D.actions_analytic n,(D.actions_analytic n).restrictScalars⟩⟩

end NLS.ZakharovShabat
