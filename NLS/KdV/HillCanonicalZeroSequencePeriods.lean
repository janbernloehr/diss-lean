import NLS.KdV.HillCommonZeroQuotientUpperBound

/-! The canonical FULL-l2 zero sequences solve the ACTUAL FULL Hill
period equations wherever their whole graph stays in one source patch.
Real-form identity transfers the physical normalization to complex
sources on a single common ball before all numerator indices. -/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem canonical_zero_sequence_equation_zero_on_ball (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (r : ℝ) (hrpos : 0 < r)
    (hU : ball q r ⊆ hillHminusCanonicalZeroSequenceDomain)
    (hgraph : ∀ y ∈ ball q r, ∀ n : ℕ+, (hillHminusCanonicalZeroSequence n y,y) ∈ P.inputDomain) :
    ∀ y ∈ ball q r, ∀ n : ℕ+, P.equation n (hillHminusCanonicalZeroSequence n y,y) = 0 := by
  intro y hy n
  apply lp.ext
  funext m
  let f : PeriodOneHminusOne → ℂ := fun z => P.equation n (hillHminusCanonicalZeroSequence n z,z) m
  have hf : AnalyticOnNhd ℂ f (ball q r) := by
    intro z hz
    have hF := (P.analytic_equation n _ (hgraph z hz n)).comp
      (f := fun a => (hillHminusCanonicalZeroSequence n a,a))
      (((analyticOnNhd_hillHminusCanonicalZeroSequence n).mono hU z hz).prod analyticAt_id)
    exact ((lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 m).analyticAt _).comp hF
  have he : EqOn f 0 (ball q r) := analytic_eqOn_of_real_periodOneHminus _ isOpen_ball
    (convex_ball q r).isPreconnected ⟨q,mem_ball_self hrpos,hr⟩ f 0 hf (fun _ _ => analyticAt_const) (by
      intro z hz hzr
      change P.equation n (hillHminusCanonicalZeroSequence n z,z) m = 0
      rw [hillHminusCanonicalZeroSequence_real n z hzr,P.equation_actual_real_zeros n z (hgraph z hz n).2 hzr]
      rfl)
  exact he hy

theorem exists_common_canonical_zero_sequence_period_ball (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ r : ℝ, 0 < r ∧ ball q r ⊆ hillHminusCanonicalZeroSequenceDomain ∧
      ∀ y ∈ ball q r, ∀ n : ℕ+,
        (hillHminusCanonicalZeroSequence n y,y) ∈ P.inputDomain ∧
        P.equation n (hillHminusCanonicalZeroSequence n y,y) = 0 := by
  obtain ⟨δ,_,hδ,_,hplace,_⟩ := P.exists_real_gapData_allDisc_quotient_upper_tube q hq hr
  obtain ⟨r,hrpos,hU,hgraphs⟩ := exists_common_zero_sequence_gapData_thickening q hr δ hδ
  have hgraph : ∀ y ∈ ball q r, ∀ n : ℕ+, (hillHminusCanonicalZeroSequence n y,y) ∈ P.inputDomain :=
    fun y hy n => hplace (hgraphs y hy n)
  exact ⟨r,hrpos,hU,fun y hy n => ⟨hgraph y hy n,
    P.canonical_zero_sequence_equation_zero_on_ball q hr r hrpos hU hgraph y hy n⟩⟩

end NLS.KdV.HillProductEquationPatch
