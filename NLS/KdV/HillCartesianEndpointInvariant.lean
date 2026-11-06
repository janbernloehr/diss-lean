import NLS.KdV.HillIntrinsicCartesianIndexedTransport

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
namespace NLS.KdV

/-- The ACTUAL single-index endpoint transport preserves the intrinsic
normalized ORIGINAL Cartesian bracket, with no proposed invariance assumption. -/
theorem exists_hillSingleEndpointTransport_preserving_normalized_bracket
    (q : RealPeriodOneHillPotential) (hmean : q.val.val 0=0)
    (n m : ℕ+) (σ τ : Bool)
    (hgapn : hillRealGapHalfLength q.val q.property.1 q.property.2 n ≠ 0)
    (hgapm : hillRealGapHalfLength q.val q.property.1 q.property.2 m ≠ 0)
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
          hillDirichletLogMultiplier q.val q.property.1 q.property.2 n hn) ∧
      hillIntrinsicNormalizedCartesianBracket n m σ τ r =
        hillIntrinsicNormalizedCartesianBracket n m σ τ q := by
  obtain ⟨γ,h0,hγ,hcons⟩ := exists_hillIndexedDiscriminant_global_integralCurve k hk q hmean
  obtain ⟨t,_,hend,hκ⟩ := exists_hillGlobalIndexedCurve_periodicTerminal k hk γ hγ
  refine ⟨⟨(γ t).val,(γ t).property⟩,(hcons t).1,(hcons t).2.1,(hcons t).2.2,?_,hκ,?_,?_,?_⟩
  · intro n hn
    have h := hillPeriodicEndpoints_eq_on_global_indexedCurve n k hn hk γ hγ t 0
    simpa only [h0] using h
  · simpa only [h0] using hend
  · intro n hn hnk
    have h := hillOtherTerminals_eq_on_global_indexedCurve n k hn hk hnk γ hγ t 0
    simpa only [h0] using h

  · have hn0 : hillRealGapHalfLength (γ 0).val (γ 0).property.1 (γ 0).property.2 n ≠ 0 := by
      simpa only [h0] using hgapn
    have hm0 : hillRealGapHalfLength (γ 0).val (γ 0).property.1 (γ 0).property.2 m ≠ 0 := by
      simpa only [h0] using hgapm
    have hi := hillIntrinsicNormalizedCartesianBracket_eq_on_global_indexedCurve
      n m ⟨k,hk⟩ σ τ γ hγ 0 t hn0 hm0
    simpa only [h0] using hi.symm

end NLS.KdV
