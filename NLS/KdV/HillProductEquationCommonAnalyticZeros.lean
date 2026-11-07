import NLS.KdV.HillProductEquationCompactBounds
import NLS.KdV.HillPeriodJacobianUniformInverse
import NLS.KdV.HillProductEquationAnalyticZeroSequence
import NLS.ComplexAnalysis.UniformAnalyticImplicitBall

/-! ONE complex source ball supports analytic full-l2 solutions of ALL
actual Hill period equations, with a common uniqueness radius in the
placed-input domain. Each branch has actual real zero-sequence agreement
as a germ; agreement on the ENTIRE common real slice is not inferred. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem exists_common_analytic_zero_sequence_ball (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ ρ ε : ℝ, 0 < ρ ∧ 0 < ε ∧ ∀ n : ℕ+,
      ∃ s : PeriodOneHminusOne → lp (fun _ : ℕ+ => ℂ) 2,
        AnalyticOnNhd ℂ s (ball q ε) ∧ s q = hillHminusPsiZeroDisplacement n ⟨q,hr⟩ ∧
        (∀ y ∈ ball q ε, (s y,y) ∈ P.inputDomain ∧ P.equation n (s y,y) = 0 ∧
          (s y,y) ∈ ball (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q) ρ ∧
          ∀ u : lp (fun _ : ℕ+ => ℂ) 2, (u,y) ∈ ball (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q) ρ →
            P.equation n (u,y) = 0 → u = s y) ∧
        ∀ᶠ a : PeriodOneRealHminusOne in 𝓝 ⟨q,hr⟩, s a.val = hillHminusPsiZeroDisplacement n a := by
  obtain ⟨R,L,hR,hL,hballs⟩ := P.exists_actual_real_uniform_equation_balls q hq hr
  obtain ⟨M,hM,hinverses⟩ := P.exists_actual_real_uniform_sequenceJacobian_equiv q hq hr
  obtain ⟨ρ,ε,hρ,hε,hρR,hIFT⟩ := exists_uniform_analytic_implicit_ball
    (E := lp (fun _ : ℕ+ => ℂ) 2) (P := PeriodOneHminusOne) R L M hR hL hM
  refine ⟨ρ,ε,hρ,hε,?_⟩
  intro n
  let d := hillHminusPsiZeroDisplacement n ⟨q,hr⟩
  have hd : d ∈ hillHminusEnergyGapData ⟨q,hr⟩ := actual_hill_zero_sequence_mem_energyGapData ⟨q,hr⟩ n
  have hball := hballs d hd
  have hballU : ball (d,q) R ⊆ P.inputDomain := ball_subset_closedBall.trans hball.1
  have hFa : AnalyticOnNhd ℂ (P.equation n) (ball (d,q) R) := (P.analytic_equation n).mono hballU
  obtain ⟨e,he,hbound⟩ := hinverses n
  obtain ⟨s,hs,hsq,hsol⟩ := hIFT (P.equation n) d q hFa
    (fun t ht => hball.2 n t (ball_subset_closedBall ht)) (P.equation_actual_real_zeros n q hq hr) e he hbound
  have hnearball : ball (d,q) ρ ⊆ P.inputDomain := (ball_subset_ball hρR.le).trans hballU
  have hrealgraph : ContinuousAt (fun a : PeriodOneRealHminusOne => (hillHminusPsiZeroDisplacement n a,a.val)) ⟨q,hr⟩ :=
    (continuous_hillHminusPsiZeroDisplacement n).continuousAt.prodMk continuous_subtype_val.continuousAt
  have hrealV : ∀ᶠ a : PeriodOneRealHminusOne in 𝓝 ⟨q,hr⟩,
      (hillHminusPsiZeroDisplacement n a,a.val) ∈ ball (d,q) ρ :=
    hrealgraph.eventually (isOpen_ball.mem_nhds (mem_ball_self hρ))
  have hrealB : ∀ᶠ a : PeriodOneRealHminusOne in 𝓝 ⟨q,hr⟩, a.val ∈ ball q ε :=
    continuous_subtype_val.continuousAt.eventually (ball_mem_nhds q hε)
  have hrealU : ∀ᶠ a : PeriodOneRealHminusOne in 𝓝 ⟨q,hr⟩, a.val ∈ P.source :=
    continuous_subtype_val.continuousAt.eventually (P.source_open.mem_nhds hq)
  refine ⟨s,hs,hsq,?_,?_⟩
  · intro y hy
    obtain ⟨hgraph,hroot,hunique⟩ := hsol y hy
    exact ⟨hnearball hgraph,hroot,hgraph,hunique⟩
  · filter_upwards [hrealV,hrealB,hrealU] with a haV haB haU
    exact ((hsol a.val haB).2.2 _ haV (P.equation_actual_real_zeros n a.val haU a.property)).symm

end NLS.KdV.HillProductEquationPatch
