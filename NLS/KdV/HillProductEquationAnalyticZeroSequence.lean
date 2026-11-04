import NLS.KdV.HillProductEquationRealInverse
import NLS.ComplexAnalysis.BanachC1ImplicitRoot

/-! For each fixed numerator index, a full complex lp-valued zero
branch exists and agrees with ALL actual real indexed zeros nearby.
The source neighborhood is not asserted uniform in the numerator index. -/
noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem exists_actual_analytic_zero_sequence (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ s : PeriodOneHminusOne → lp (fun _ : ℕ+ => ℂ) 2,
      AnalyticAt ℂ s q ∧ s q = hillHminusPsiZeroDisplacement n ⟨q,hr⟩ ∧
      (∀ᶠ y in 𝓝 q, (s y,y) ∈ P.inputDomain ∧ P.equation n (s y,y) = 0) ∧
      ∀ᶠ a : PeriodOneRealHminusOne in 𝓝 ⟨q,hr⟩, s a.val = hillHminusPsiZeroDisplacement n a := by
  let d := hillHminusPsiZeroDisplacement n ⟨q,hr⟩
  have ht : (d,q) ∈ P.inputDomain := P.actual_real_graph_mem q hq hr n
  have hF : AnalyticAt ℂ (P.equation n) (d,q) := P.analytic_equation n (d,q) ht
  have hz : P.equation n (d,q) = 0 := P.equation_actual_real_zeros n q hq hr
  have hbij := P.sequenceJacobian_actual_real_bijective n q hq hr
  obtain ⟨s,V,hV,hbase,hsc1,hsq,hunique,hzeros⟩ := exists_C1_implicitBanachRoot_unique
    (P.equation n) d q hF.contDiffAt hz hbij
  have hFs : AnalyticAt ℂ (P.equation n) (s q,q) := by rw [hsq]; exact hF
  have hbs : Function.Bijective ((fderiv ℂ (P.equation n) (s q,q)).comp
      (ContinuousLinearMap.inl ℂ (lp (fun _ : ℕ+ => ℂ) 2) PeriodOneHminusOne)) := by
    rw [hsq]
    exact hbij
  have hs : AnalyticAt ℂ s q := analyticAt_implicitBanachRoot (P.equation n) s q hFs hsc1.continuousAt hzeros hbs
  have hgraph : ContinuousAt (fun y : PeriodOneHminusOne => (s y,y)) q := hs.continuousAt.prodMk continuousAt_id
  have hinput : ∀ᶠ y in 𝓝 q, (s y,y) ∈ P.inputDomain := by
    apply hgraph.eventually (P.inputDomain_open.mem_nhds ?_)
    change (s q,q) ∈ P.inputDomain
    rwa [hsq]
  have hrealgraph : ContinuousAt (fun a : PeriodOneRealHminusOne => (hillHminusPsiZeroDisplacement n a,a.val)) ⟨q,hr⟩ :=
    (continuous_hillHminusPsiZeroDisplacement n).continuousAt.prodMk continuous_subtype_val.continuousAt
  have hrealV : ∀ᶠ a : PeriodOneRealHminusOne in 𝓝 ⟨q,hr⟩,
      (hillHminusPsiZeroDisplacement n a,a.val) ∈ V := hrealgraph.eventually (hV.mem_nhds hbase)
  have hrealU : ∀ᶠ a : PeriodOneRealHminusOne in 𝓝 ⟨q,hr⟩, a.val ∈ P.source :=
    continuous_subtype_val.continuousAt.eventually (P.source_open.mem_nhds hq)
  refine ⟨s,hs,hsq,?_,?_⟩
  · filter_upwards [hinput,hzeros] with y hy hz
    exact ⟨hy,hz⟩
  · filter_upwards [hrealV,hrealU] with a haV haU
    exact (hunique _ a.val haV (P.equation_actual_real_zeros n a.val haU a.property)).symm

end NLS.KdV.HillProductEquationPatch
