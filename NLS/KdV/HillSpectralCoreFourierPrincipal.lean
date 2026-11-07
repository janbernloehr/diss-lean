import NLS.KdV.HillSpectralCoreDiracModel
import NLS.SequenceSpaces.PeriodOneMiuraCompactDerivative
import NLS.SequenceSpaces.MeanZeroHalfFourierEquiv

/-! The fixed massive principal part is exactly the original half-Fourier
operator composed with identity minus the compact massive resolvent term.
This fixes both signed Fourier constants before any Fredholm argument. -/
noncomputable section
open Complex NLS.ZakharovShabat
namespace NLS.KdV

/-- The exact fixed principal operator differs from the original free
half-Fourier map only by its actual compact mass correction. -/
theorem hillSpectralCoreDiracPrincipal_eq_halfFourier :
    hillSpectralCoreDiracPrincipal = (WeightedCoeff.halfFourierEquiv 2).toContinuousLinearMap.comp
      (ContinuousLinearMap.id ℂ PeriodOneHminusOne-periodOneL2Inclusion.comp (periodOneMassInverse 0)) := by
  apply ContinuousLinearMap.ext
  intro q
  let u := periodOneMassInverse 0 q
  let w := Weight.signedSobolev (-1/2)
  have hmass (k : ℤ) : q.val k = periodOneMassSymbol 0 k*u k := by
    have he := congrArg (fun a : PeriodOneHminusOne => a.val k) (periodOneMassOperator_inverse 0 q)
    rw [periodOneMassOperator_apply] at he
    exact he.symm
  have herr (k : ℤ) : q.val k-u k = 2*I*(Real.pi : ℂ)*k*u k := by
    rw [hmass]
    simp only [periodOneMassSymbol,Nat.cast_zero,zero_add,ofReal_one]
    ring
  apply (WeightedCoeff.weightIsometry w 2).injective
  ext k
  change (WeightedCoeff.weightIsometry w 2
    (sourceHillTerminalFourier (sourcePhase (hillMiuraDiagonal u)))) k =
      (w k : ℂ)*(WeightedCoeff.halfFourierSymbol k*(q.val k-(periodOneL2Inclusion u).val k))
  rw [sourceHillTerminalFourier_weighted_apply,periodOneL2Inclusion_apply,herr]
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · let n : ℕ+ := ⟨k.natAbs,Int.natAbs_pos.mpr (by omega)⟩
    have hnk : -((n:ℕ):ℤ) = k := by change -(k.natAbs : ℤ) = k; omega
    rw [sourceSignedTerminalFourier_negative _ k hk,sourcePhase_fst,hillMiuraDiagonal_fst]
    simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul]
    have hnrm := WeightedCoeff.signedHalf_halfFourier_derivative_normalization_negative n (u k)
    rw [hnk] at hnrm
    have hnC : -(((n:ℕ):ℤ):ℂ) = (k:ℂ) := by rw [← Int.cast_neg,hnk]
    rw [hnC] at hnrm
    change (w k : ℂ)*WeightedCoeff.halfFourierSymbol k*(2*I*(Real.pi : ℂ)*k*u k) =
      -2*I*sourceHillTerminalScale*u k at hnrm
    calc
      _ = -2*I*sourceHillTerminalScale*u k := by ring
      _ = _ := by rw [← hnrm]; ring
  · have hfree : sourceSignedTerminalFourier (sourcePhase (hillMiuraDiagonal u)) 0 = 0 :=
      Coeff.signedPositiveSplice_zero _ _
    rw [hfree]
    simp only [Int.cast_zero,mul_zero,zero_mul]
  · let n : ℕ+ := ⟨k.natAbs,Int.natAbs_pos.mpr (by omega)⟩
    have hnk : ((n:ℕ):ℤ) = k := by change (k.natAbs : ℤ) = k; omega
    rw [sourceSignedTerminalFourier_positive _ k hk,sourcePhase_snd,hillMiuraDiagonal_snd]
    simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul]
    have hnrm := WeightedCoeff.signedHalf_halfFourier_derivative_normalization n (u k)
    rw [hnk] at hnrm
    have hnC : ((n:ℕ):ℂ) = (k:ℂ) := by exact_mod_cast hnk
    rw [hnC] at hnrm
    change (w k : ℂ)*WeightedCoeff.halfFourierSymbol k*(2*I*(Real.pi : ℂ)*k*u k) =
      2*I*sourceHillTerminalScale*u k at hnrm
    calc
      _ = 2*I*sourceHillTerminalScale*u k := by ring
      _ = _ := by rw [← hnrm]; ring

theorem isCompactOperator_hillSpectralCoreDiracPrincipal_sub_halfFourier :
    IsCompactOperator (hillSpectralCoreDiracPrincipal-(WeightedCoeff.halfFourierEquiv 2).toContinuousLinearMap) := by
  have he : hillSpectralCoreDiracPrincipal-(WeightedCoeff.halfFourierEquiv 2).toContinuousLinearMap =
      -((WeightedCoeff.halfFourierEquiv 2).toContinuousLinearMap.comp
        (periodOneL2Inclusion.comp (periodOneMassInverse 0))) := by
    rw [hillSpectralCoreDiracPrincipal_eq_halfFourier]
    apply ContinuousLinearMap.ext
    intro q
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,sub_apply,neg_apply,map_sub]
    abel
  rw [he]
  exact ((isCompactOperator_periodOneL2Inclusion.comp_clm (periodOneMassInverse 0)).clm_comp
    (WeightedCoeff.halfFourierEquiv 2).toContinuousLinearMap).neg

/-- Every physical source has a constructed common complex neighborhood
where its actual core derivative is a compact perturbation of the exact free Fourier map. -/
theorem exists_hillSpectralCore_compact_halfFourier_neighborhood (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) :
    ∃ P : HillProductEquationPatch, ∃ U : Set PeriodOneHminusOne,
      IsOpen U ∧ q ∈ U ∧ U ⊆ P.physicalDirichletSource ∩ hillHminusActionAngleNativeDomain ∧
      AnalyticOnNhd ℂ P.physicalSpectralCoreMap U ∧
      (∀ a ∈ U, IsCompactOperator (fderiv ℂ P.physicalSpectralCoreMap a-
        (WeightedCoeff.halfFourierEquiv 2).toContinuousLinearMap)) ∧
      (∀ a : HillMeanZeroSource, a.val ∈ U → IsCompactOperator (P.physicalMeanZeroSpectralCoreRemainder a)) := by
  obtain ⟨P,U,hU,hq,hUP,ha,_,hc,hm⟩ := exists_hillSpectralCore_Dirac_model q hr
  refine ⟨P,U,hU,hq,hUP,ha,fun a ha => ?_,hm⟩
  have he : fderiv ℂ P.physicalSpectralCoreMap a-(WeightedCoeff.halfFourierEquiv 2).toContinuousLinearMap =
      (fderiv ℂ P.physicalSpectralCoreMap a-hillSpectralCoreDiracPrincipal)+
        (hillSpectralCoreDiracPrincipal-(WeightedCoeff.halfFourierEquiv 2).toContinuousLinearMap) := by abel
  rw [he]
  exact (hc a ha).add isCompactOperator_hillSpectralCoreDiracPrincipal_sub_halfFourier

end NLS.KdV
