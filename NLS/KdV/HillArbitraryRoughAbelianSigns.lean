import NLS.KdV.HillArbitraryRoughPhysicalUniqueness
import NLS.KdV.HillRegularTerminalDensity
import NLS.ComplexAnalysis.AnalyticGermSign

/-! # Physical Abelian squares determine a constant rough sign away from zero

The actual nonzero-sheet locus is dense at every physical base. Its
restriction can therefore be removed by continuity before native rough
real-form uniqueness and analytic sign selection are applied.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV

theorem eqOn_rough_domain_sq_of_physical_sheet_eq
    (U : Set PeriodOneHminusOne) (hU : IsOpen U) (hconn : IsPreconnected U)
    (q0 : PeriodOneHminusOne) (hq0 : q0 ∈ U) (hr0 : IsRealPeriodOneHminusOne q0)
    (n : ℕ+) (f g : PeriodOneHminusOne → ℂ) (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (he : ∀ p : RealPeriodOneHillPotential, (hillPhysicalHminusEmbedding p).val ∈ U →
      hillDirichletSheetRoot (SpectralWeight.one.toCoeff p.val)
        (hillDirichletEnergy p.val p.property.1 p.property.2 n n.property) ≠ 0 →
      (f (hillPhysicalHminusEmbedding p).val)^2 = (g (hillPhysicalHminusEmbedding p).val)^2) :
    EqOn (fun q => (f q)^2) (fun q => (g q)^2) U := by
  let L : RealPeriodOneHillPotential → PeriodOneHminusOne := fun p => (hillPhysicalHminusEmbedding p).val
  have hL : Continuous L := continuous_subtype_val.comp continuous_hillPhysicalHminusEmbedding
  let V := L ⁻¹' U
  have hV : IsOpen V := hU.preimage hL
  have hFc : ContinuousOn (fun p => (f (L p))^2) V :=
    (hf.pow 2).continuousOn.comp hL.continuousOn (fun _ h => h)
  have hGc : ContinuousOn (fun p => (g (L p))^2) V :=
    (hg.pow 2).continuousOn.comp hL.continuousOn (fun _ h => h)
  let S := {p : RealPeriodOneHillPotential | hillDirichletSheetRoot (SpectralWeight.one.toCoeff p.val)
    (hillDirichletEnergy p.val p.property.1 p.property.2 n n.property) ≠ 0}
  have hS : Dense S := dense_hillDirichletSheetRoot_ne_zero n n.property
  have hEq : EqOn (fun p => (f (L p))^2) (fun p => (g (L p))^2) (V ∩ S) :=
    fun p hp => he p hp.1 hp.2
  have hfull : EqOn (fun p => (f (L p))^2) (fun p => (g (L p))^2) V :=
    hEq.of_subset_closure hFc hGc inter_subset_left (fun p hp => hV.inter_closure ⟨hp,hS p⟩)
  exact eqOn_rough_domain_of_physical_eq U hU hconn q0 hq0 hr0 _ _ (hf.pow 2) (hg.pow 2)
    (fun p hp => hfull hp)

theorem eqOn_or_neg_rough_domain_of_physical_abelian_sq
    (U : Set PeriodOneHminusOne) (hU : IsOpen U) (hconn : IsPreconnected U)
    (q0 : PeriodOneHminusOne) (hq0 : q0 ∈ U) (hr0 : IsRealPeriodOneHminusOne q0)
    (n : ℕ+) (f g : PeriodOneHminusOne → ℂ) (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (he : ∀ p : RealPeriodOneHillPotential, (hillPhysicalHminusEmbedding p).val ∈ U →
      hillDirichletSheetRoot (SpectralWeight.one.toCoeff p.val)
        (hillDirichletEnergy p.val p.property.1 p.property.2 n n.property) ≠ 0 →
      (f (hillPhysicalHminusEmbedding p).val)^2 = (g (hillPhysicalHminusEmbedding p).val)^2) :
    EqOn f g U ∨ EqOn f (fun q => -g q) U := by
  have hsq := eqOn_rough_domain_sq_of_physical_sheet_eq U hU hconn q0 hq0 hr0 n f g hf hg he
  have hnear : ∀ᶠ q in 𝓝 q0, (f q)^2 = (g q)^2 := by
    filter_upwards [hU.mem_nhds hq0] with q hq
    exact hsq hq
  rcases analytic_germ_eq_or_eq_neg_of_sq_eq (hf q0 hq0) (hg q0 hq0) hnear with h | h
  · exact Or.inl (hf.eqOn_of_preconnected_of_eventuallyEq hg hconn hq0 h)
  · exact Or.inr (hf.eqOn_of_preconnected_of_eventuallyEq (fun q hq => (hg q hq).neg) hconn hq0 h)

end NLS.KdV
