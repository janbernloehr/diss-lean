import NLS.KdV.HillEndpointReachability

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- Every unselected physical Dirichlet energy and log-norming coordinate
is constant on an actual complete indexed trajectory. -/
theorem hillOtherTerminals_eq_on_global_indexedCurve
    (n k : ℕ) (hn : 1≤n) (hk : 1≤k) (hnk : n≠k)
    (γ : ℝ → hillRealSourceSubmodule)
    (hγ : ∀ t : ℝ, HasDerivAt γ (hillRealIndexedDiscriminantField k hk (γ t)) t)
    (u v : ℝ) :
    hillDirichletEnergy (γ u).val (γ u).property.1 (γ u).property.2 n hn=
      hillDirichletEnergy (γ v).val (γ v).property.1 (γ v).property.2 n hn ∧
    hillDirichletLogMultiplier (γ u).val (γ u).property.1 (γ u).property.2 n hn=
      hillDirichletLogMultiplier (γ v).val (γ v).property.1 (γ v).property.2 n hn := by
  have hμ (t : ℝ) := hasDerivAt_hillDirichletEnergy_indexed_integralCurve n k hn hk γ t (hγ t)
  have hκ (t : ℝ) := hasDerivAt_hillLogMultiplier_indexed_integralCurve n k hn hk γ t (hγ t)
  simp only [if_neg hnk] at hμ hκ
  exact ⟨Complex.ofReal_injective (is_const_of_deriv_eq_zero
      (fun t => (hμ t).differentiableAt) (fun t => (hμ t).deriv) u v),
    Complex.ofReal_injective (is_const_of_deriv_eq_zero
      (fun t => (hκ t).differentiableAt) (fun t => (hκ t).deriv) u v)⟩

/-- An original mean-zero rough Hill source can be transported to a selected
periodic terminal by its actual indexed spectral flow. The original norm,
mean, all-energy discriminant, all periodic endpoints and every other
Dirichlet energy and log-norming coordinate are preserved. -/
theorem exists_hillSingleEndpointTransport
    (q : RealPeriodOneHillPotential) (hmean : q.val.val 0=0)
    (k : ℕ) (hk : 1≤k) :
    ∃ r : RealPeriodOneHillPotential,
      r.val.val 0=0 ∧ ‖r.val‖=‖q.val‖ ∧
      (∀ E : ℂ, hillL2Discriminant (SpectralWeight.one.toCoeff r.val) E=
        hillL2Discriminant (SpectralWeight.one.toCoeff q.val) E) ∧
      (∀ n : ℕ, 1≤n →
        hillRealLabels r.val r.property.1 r.property.2 (2*n-1)=
          hillRealLabels q.val q.property.1 q.property.2 (2*n-1) ∧
        hillRealLabels r.val r.property.1 r.property.2 (2*n)=
          hillRealLabels q.val q.property.1 q.property.2 (2*n)) ∧
      hillDirichletLogMultiplier r.val r.property.1 r.property.2 k hk=0 ∧
      (hillDirichletEnergy r.val r.property.1 r.property.2 k hk=
        hillRealLabels q.val q.property.1 q.property.2 (2*k-1) ∨
       hillDirichletEnergy r.val r.property.1 r.property.2 k hk=
        hillRealLabels q.val q.property.1 q.property.2 (2*k)) ∧
      (∀ n : ℕ, ∀ hn : 1≤n, n≠k →
        hillDirichletEnergy r.val r.property.1 r.property.2 n hn=
          hillDirichletEnergy q.val q.property.1 q.property.2 n hn ∧
        hillDirichletLogMultiplier r.val r.property.1 r.property.2 n hn=
          hillDirichletLogMultiplier q.val q.property.1 q.property.2 n hn) := by
  obtain ⟨γ,h0,hγ,hcons⟩ := exists_hillIndexedDiscriminant_global_integralCurve k hk q hmean
  obtain ⟨t,_,hend,hκ⟩ := exists_hillGlobalIndexedCurve_periodicTerminal k hk γ hγ
  refine ⟨⟨(γ t).val,(γ t).property⟩,(hcons t).1,(hcons t).2.1,(hcons t).2.2,?_,hκ,?_,?_⟩
  · intro n hn
    have h := hillPeriodicEndpoints_eq_on_global_indexedCurve n k hn hk γ hγ t 0
    simpa only [h0] using h
  · simpa only [h0] using hend
  · intro n hn hnk
    have h := hillOtherTerminals_eq_on_global_indexedCurve n k hn hk hnk γ hγ t 0
    simpa only [h0] using h

end NLS.KdV
