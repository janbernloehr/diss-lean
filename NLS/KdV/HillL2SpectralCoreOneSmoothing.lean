import NLS.KdV.HillL2TerminalModelOneSmoothing

/-! Genuine one-smoothing of the ACTUAL physical Hill spectral core.
At every real L2 source, construct one complex open L2 neighborhood
before all modes. Its analytic native H3/2 remainder has exactly the
original physical-core-minus-free-Fourier coefficients. -/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat
namespace NLS.KdV

private theorem eventually_L2_mem_open (q : Coeff 2) (V : Set PeriodOneHminusOne)
    (hV : IsOpen V) (hqV : periodOneL2Inclusion q ∈ V) :
    ∀ᶠ r in 𝓝 q, periodOneL2Inclusion r ∈ V :=
  periodOneL2Inclusion.continuous.continuousAt.tendsto.eventually (hV.mem_nhds hqV)

private theorem actual_core_raw_of_model (P : HillProductEquationPatch)
    (r : Coeff 2) (k : ℤ)
    (hmodel : P.physicalSpectralCoreMap (periodOneL2Inclusion r) =
      sourceHillTerminalModel (P.rotatedDiracSource (periodOneL2Inclusion r)))
    (hraw : (P.l2TerminalModelFourierRemainder r).val k =
      (sourceHillTerminalModel (P.rotatedDiracSource (periodOneL2Inclusion r))).val k -
        WeightedCoeff.halfFourierSymbol k * r k) :
    (P.l2TerminalModelFourierRemainder r).val k =
      (P.physicalSpectralCoreMap (periodOneL2Inclusion r)).val k -
        WeightedCoeff.halfFourierSymbol k * r k :=
  hraw.trans (congrArg (fun a : WeightedCoeff (Weight.signedSobolev (-1/2)) 2 =>
    a.val k - WeightedCoeff.halfFourierSymbol k * r k) hmodel.symm)

theorem exists_hillL2SpectralCore_one_smoothing (q : Coeff 2)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    ∃ P : HillProductEquationPatch, ∃ U : Set (Coeff 2), IsOpen U ∧ q ∈ U ∧
      (∀ r ∈ U, periodOneL2Inclusion r ∈ P.physicalDirichletSource ∩ hillHminusActionAngleNativeDomain) ∧
      AnalyticOnNhd ℂ P.l2TerminalModelFourierRemainder U ∧
      ∀ r ∈ U, ∀ k : ℤ, (P.l2TerminalModelFourierRemainder r).val k =
        (P.physicalSpectralCoreMap (periodOneL2Inclusion r)).val k -
          WeightedCoeff.halfFourierSymbol k * r k := by
  obtain ⟨P,V,hV,hqV,hVP,_,hmodel,_,_⟩ := exists_hillSpectralCore_Dirac_model (periodOneL2Inclusion q) hr
  have hqP : periodOneL2Inclusion q ∈ P.source := (hVP hqV).1.1
  have hdata := P.eventually_l2TerminalModelFourierRemainder_data q hqP hr
  have hall : ∀ᶠ r in 𝓝 q,
      periodOneL2Inclusion r ∈ P.physicalDirichletSource ∩ hillHminusActionAngleNativeDomain ∧
      AnalyticAt ℂ P.l2TerminalModelFourierRemainder r ∧ ∀ k : ℤ,
        (P.l2TerminalModelFourierRemainder r).val k =
          (P.physicalSpectralCoreMap (periodOneL2Inclusion r)).val k -
            WeightedCoeff.halfFourierSymbol k * r k :=
    ((eventually_L2_mem_open q V hV hqV).and hdata).mono (fun r h =>
      ⟨hVP h.1,h.2.1,fun k => actual_core_raw_of_model P r k (hmodel _ h.1) (h.2.2 k)⟩)
  obtain ⟨U,hUsub,hU,hqU⟩ := _root_.mem_nhds_iff.mp hall
  exact ⟨P,U,hU,hqU,fun r hrU => (hUsub hrU).1,fun r hrU => (hUsub hrU).2.1,
    fun r hrU => (hUsub hrU).2.2⟩

end NLS.KdV
