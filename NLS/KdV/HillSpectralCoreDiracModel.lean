import NLS.KdV.HillSpectralCoreNeighborhood
import NLS.KdV.HillDiracSpectralTerminal
import NLS.KdV.HillRotatedDiracSource
import NLS.ZakharovShabat.SourceHillWeightedTerminalModel
import NLS.SequenceSpaces.SignedHalfTerminalNormalization

/-! The actual Hill spectral core equals the native weighted Dirac model
on a constructed common complex neighborhood. Its derivative differs
compactly from one fixed, explicitly normalized massive Fourier operator. -/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat
namespace NLS.KdV

/-- The fixed native weighted Fourier principal part of the Hill core. -/
def hillSpectralCoreDiracPrincipal :
    PeriodOneHminusOne →L[ℂ] WeightedCoeff (Weight.signedSobolev (-1/2)) 2 :=
  sourceHillTerminalFourier.comp ((sourcePhase.comp hillMiuraDiagonal).comp (periodOneMassInverse 0))

/-- At every original physical source, construct one complex neighborhood
before all modes, with the actual model identity and compact principal remainder. -/
theorem exists_hillSpectralCore_Dirac_model (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) :
    ∃ P : HillProductEquationPatch, ∃ U : Set PeriodOneHminusOne,
      IsOpen U ∧ q ∈ U ∧ U ⊆ P.physicalDirichletSource ∩ hillHminusActionAngleNativeDomain ∧
      AnalyticOnNhd ℂ P.physicalSpectralCoreMap U ∧
      (∀ a ∈ U, P.physicalSpectralCoreMap a = sourceHillTerminalModel (P.rotatedDiracSource a)) ∧
      (∀ a ∈ U, IsCompactOperator (fderiv ℂ P.physicalSpectralCoreMap a-hillSpectralCoreDiracPrincipal)) ∧
      (∀ a : HillMeanZeroSource, a.val ∈ U → IsCompactOperator (P.physicalMeanZeroSpectralCoreRemainder a)) := by
  obtain ⟨P,V,hV,hqV,hVP,hcore,hcoords,_,hmean⟩ := exists_hillSpectralCoreNeighborhood q hr
  obtain ⟨W,hW,hreal,hmodel,hmdata⟩ := exists_sourceHillTerminalModel_compact_derivative_domain
  have hqP : q ∈ P.source := (hVP hqV).1.1
  have hqW : P.rotatedDiracSource q ∈ W := hreal (P.isRealType_rotatedDiracSource q hqP hr)
  have hpre : P.rotatedDiracSource ⁻¹' W ∈ 𝓝 q :=
    (P.analytic_rotatedDiracSource q hqP).continuousAt.preimage_mem_nhds (hW.mem_nhds hqW)
  obtain ⟨U,hUsub,hU,hqU⟩ := _root_.mem_nhds_iff.mp (inter_mem (hV.mem_nhds hqV) hpre)
  have hUP : U ⊆ P.physicalDirichletSource ∩ hillHminusActionAngleNativeDomain :=
    fun a ha => hVP (hUsub ha).1
  have heq (a : PeriodOneHminusOne) (ha : a ∈ U) :
      P.physicalSpectralCoreMap a = sourceHillTerminalModel (P.rotatedDiracSource a) := by
    let ψ := P.rotatedDiracSource a
    have haP : a ∈ P.source := (hUP ha).1.1
    have haW : ψ ∈ W := (hUsub ha).2
    apply (WeightedCoeff.weightIsometry (Weight.signedSobolev (-1/2)) 2).injective
    ext k
    rcases lt_trichotomy k 0 with hk | rfl | hk
    · let n : ℕ+ := ⟨k.natAbs,Int.natAbs_pos.mpr (by omega)⟩
      have hnk : -((n:ℕ):ℤ) = k := by change -(k.natAbs : ℤ) = k; omega
      rw [← hnk]
      change (Weight.signedSobolev (-1/2) (-((n:ℕ):ℤ)) : ℂ)*
        (P.physicalSpectralCoreMap a).val (-((n:ℕ):ℤ)) = _
      rw [(hcoords a (hUsub ha).1 n).2,P.physicalSpectralFactorPlus_eq_rotatedTerminal n a haP,
        WeightedCoeff.signedHalf_terminal_normalization_negative]
      rw [((hmdata ψ haW).1 n).2]
      simp only [sourceHillTerminalScale,sourcePositiveNormalizedMidpoint,ψ,
        HillProductEquationPatch.rotatedDiracSource,canonicalPeriodicMidpoint_sourcePhase]
    · change (Weight.signedSobolev (-1/2) 0 : ℂ)*(P.physicalSpectralCoreMap a).val 0 =
        (Weight.signedSobolev (-1/2) 0 : ℂ)*(sourceHillTerminalModel ψ).val 0
      rw [P.physicalSpectralCoreMap_zero_mode,sourceHillTerminalModel_zero_mode]
    · let n : ℕ+ := ⟨k.natAbs,Int.natAbs_pos.mpr (by omega)⟩
      have hnk : ((n:ℕ):ℤ) = k := by change (k.natAbs : ℤ) = k; omega
      rw [← hnk]
      change (Weight.signedSobolev (-1/2) ((n:ℕ):ℤ) : ℂ)*
        (P.physicalSpectralCoreMap a).val ((n:ℕ):ℤ) = _
      rw [(hcoords a (hUsub ha).1 n).1,P.physicalSpectralFactorMinus_eq_rotatedTerminal n a haP,
        WeightedCoeff.signedHalf_terminal_normalization]
      rw [((hmdata ψ haW).1 n).1]
      simp only [sourceHillTerminalScale,sourcePositiveNormalizedMidpoint,ψ,
        HillProductEquationPatch.rotatedDiracSource,canonicalPeriodicMidpoint_sourcePhase]
  refine ⟨P,U,hU,hqU,hUP,hcore.mono (fun a ha => (hUsub ha).1),heq,?_,
    fun a ha => hmean a (hUsub ha).1⟩
  intro a ha
  have haP : a ∈ P.source := (hUP ha).1.1
  have haW : P.rotatedDiracSource a ∈ W := (hUsub ha).2
  have hdf : fderiv ℂ P.physicalSpectralCoreMap a =
      (fderiv ℂ sourceHillTerminalModel (P.rotatedDiracSource a)).comp
        (fderiv ℂ P.rotatedDiracSource a) := by
    have he : P.physicalSpectralCoreMap =ᶠ[𝓝 a] fun b => sourceHillTerminalModel (P.rotatedDiracSource b) := by
      filter_upwards [hU.mem_nhds ha] with b hb
      exact heq b hb
    rw [he.fderiv_eq]
    exact ((hmodel _ haW).differentiableAt.hasFDerivAt.comp a
      (P.analytic_rotatedDiracSource a haP).differentiableAt.hasFDerivAt).fderiv
  have he : fderiv ℂ P.physicalSpectralCoreMap a-hillSpectralCoreDiracPrincipal =
      (fderiv ℂ sourceHillTerminalModel (P.rotatedDiracSource a)-sourceHillTerminalFourier).comp
        (fderiv ℂ P.rotatedDiracSource a)+sourceHillTerminalFourier.comp
          (fderiv ℂ P.rotatedDiracSource a-(sourcePhase.comp hillMiuraDiagonal).comp (periodOneMassInverse 0)) := by
    rw [hdf]
    apply ContinuousLinearMap.ext
    intro h
    simp only [hillSpectralCoreDiracPrincipal,ContinuousLinearMap.comp_apply,sub_apply,add_apply,map_sub]
    abel
  rw [he]
  exact (((hmdata _ haW).2).comp_clm (fderiv ℂ P.rotatedDiracSource a)).add
    ((P.isCompactOperator_rotatedDiracSourceDerivative_sub_massInverse a haP).clm_comp sourceHillTerminalFourier)

end NLS.KdV
