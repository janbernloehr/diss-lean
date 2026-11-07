import NLS.KdV.HillSpectralCoreDiracModel

/-! The actual core/Dirac identity on an ARBITRARY retained original
patch with its verified estimates. Neither the patch nor its family
is reselected, so later on-index estimates use the SAME objects. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat
namespace NLS.KdV.HillProductEquationPatch

private theorem core_eq_model_of_signed_data (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (q : PeriodOneHminusOne) (hq : q ∈ P.physicalDirichletSource)
    (hnat : q ∈ hillHminusActionAngleNativeDomain)
    (hc : ∀ n : ℕ+, hillHminusDiagonalCartesianPlus n q = P.physicalOnIndexCartesianPlus n q ∧
      hillHminusDiagonalCartesianMinus n q = P.physicalOnIndexCartesianMinus n q)
    (hm : ∀ n : ℕ+,
      (WeightedCoeff.weightIsometry (Weight.signedSobolev (-1/2)) 2
        (sourceHillTerminalModel (P.rotatedDiracSource q))) ((n : ℕ) : ℤ) =
          sourceHillTerminalScale * sourcePositiveNormalizedMidpoint (by simp) (by norm_num) n (P.rotatedDiracSource q) *
            sourceGapWeightedEtaTerminalCoordinate (by simp) (by norm_num) ((n : ℕ) : ℤ) 1 (P.rotatedDiracSource q) ∧
      (WeightedCoeff.weightIsometry (Weight.signedSobolev (-1/2)) 2
        (sourceHillTerminalModel (P.rotatedDiracSource q))) (-((n : ℕ) : ℤ)) =
          sourceHillTerminalScale * sourcePositiveNormalizedMidpoint (by simp) (by norm_num) n (P.rotatedDiracSource q) *
            sourceGapWeightedEtaTerminalCoordinate (by simp) (by norm_num) ((n : ℕ) : ℤ) (-1) (P.rotatedDiracSource q)) :
    P.physicalSpectralCoreMap q = sourceHillTerminalModel (P.rotatedDiracSource q) := by
  apply (WeightedCoeff.weightIsometry (Weight.signedSobolev (-1/2)) 2).injective
  ext k
  rcases lt_trichotomy k 0 with hk | hk | hk
  · let n : ℕ+ := ⟨k.natAbs,Int.natAbs_pos.mpr (by omega)⟩
    have hnk : -((n : ℕ) : ℤ) = k := by change -(k.natAbs : ℤ) = k; omega
    rw [← hnk]
    change (Weight.signedSobolev (-1/2) (-((n : ℕ) : ℤ)) : ℂ) *
      (P.physicalSpectralCoreMap q).val (-((n : ℕ) : ℤ)) = _
    rw [P.physicalSpectralCoreMap_negative H q hq hnat n (hc n).1,
      P.physicalSpectralFactorPlus_eq_rotatedTerminal n q hq.1,
      WeightedCoeff.signedHalf_terminal_normalization_negative,(hm n).2]
    simp only [sourceHillTerminalScale,sourcePositiveNormalizedMidpoint,rotatedDiracSource,
      canonicalPeriodicMidpoint_sourcePhase]
  · subst k
    change (Weight.signedSobolev (-1/2) 0 : ℂ) * (P.physicalSpectralCoreMap q).val 0 =
      (Weight.signedSobolev (-1/2) 0 : ℂ) * (sourceHillTerminalModel (P.rotatedDiracSource q)).val 0
    rw [P.physicalSpectralCoreMap_zero_mode,sourceHillTerminalModel_zero_mode]
  · let n : ℕ+ := ⟨k.natAbs,Int.natAbs_pos.mpr (by omega)⟩
    have hnk : ((n : ℕ) : ℤ) = k := by change (k.natAbs : ℤ) = k; omega
    rw [← hnk]
    change (Weight.signedSobolev (-1/2) ((n : ℕ) : ℤ) : ℂ) *
      (P.physicalSpectralCoreMap q).val ((n : ℕ) : ℤ) = _
    rw [P.physicalSpectralCoreMap_positive H q hq hnat n (hc n).2,
      P.physicalSpectralFactorMinus_eq_rotatedTerminal n q hq.1,
      WeightedCoeff.signedHalf_terminal_normalization,(hm n).1]
    simp only [sourceHillTerminalScale,sourcePositiveNormalizedMidpoint,rotatedDiracSource,
      canonicalPeriodicMidpoint_sourcePhase]

private theorem eventually_rotated_model_domain (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (W : Set (CoeffPair 2))
    (hW : IsOpen W) (hqW : P.rotatedDiracSource q ∈ W) :
    ∀ᶠ a in 𝓝 q, P.rotatedDiracSource a ∈ W :=
  (P.analytic_rotatedDiracSource q hq).continuousAt.tendsto.eventually (hW.mem_nhds hqW)

theorem exists_retained_core_Dirac_identity_neighborhood (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧
      (∀ a ∈ U, a ∈ P.physicalDirichletSource ∩ hillHminusActionAngleNativeDomain) ∧
      ∀ a ∈ U, P.physicalSpectralCoreMap a = sourceHillTerminalModel (P.rotatedDiracSource a) := by
  obtain ⟨r,hrpos,hsub,hcart⟩ := exists_common_intrinsic_diagonal_Cartesian_patch_ball P q hq hr
  obtain ⟨W,hW,hreal,_,hmdata⟩ := exists_sourceHillTerminalModel_compact_derivative_domain
  have hqW : P.rotatedDiracSource q ∈ W := hreal (P.isRealType_rotatedDiracSource q hq hr)
  have hball : ∀ᶠ a in 𝓝 q, a ∈ ball q r := isOpen_ball.mem_nhds (mem_ball_self hrpos)
  have hnat : ∀ᶠ a in 𝓝 q, a ∈ hillHminusActionAngleNativeDomain :=
    isOpen_hillHminusActionAngleNativeDomain.mem_nhds (real_mem_hillHminusActionAngleNativeDomain q hr)
  have hall : ∀ᶠ a in 𝓝 q,
      a ∈ P.physicalDirichletSource ∩ hillHminusActionAngleNativeDomain ∧
        P.physicalSpectralCoreMap a = sourceHillTerminalModel (P.rotatedDiracSource a) :=
    (hball.and (hnat.and (P.eventually_rotated_model_domain q hq W hW hqW))).mono (fun a h =>
      ⟨⟨(hsub h.1).1,h.2.1⟩,P.core_eq_model_of_signed_data H a (hsub h.1).1 h.2.1
        (fun n => hcart n a h.1) (fun n => (hmdata _ h.2.2).1 n)⟩)
  obtain ⟨U,hUsub,hU,hqU⟩ := _root_.mem_nhds_iff.mp hall
  exact ⟨U,hU,hqU,fun a ha => (hUsub ha).1,fun a ha => (hUsub ha).2⟩

end NLS.KdV.HillProductEquationPatch
