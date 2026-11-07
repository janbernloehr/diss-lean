import NLS.ZakharovShabat.SourceDirichletTerminalJacobianCompact
import NLS.SequenceSpaces.SignedPositiveSplice

/-! Select the positive Dirac labels for both Hill signs. This bounded
linear splice preserves the actual terminal analyticity and compact
Fourier derivative estimate, with the central mode exactly zero. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

def sourceSignedTerminalSequence (ψ : CoeffPair 2) : Coeff 2 :=
  Coeff.signedPositiveSplice
    (sourceGapWeightedEtaTerminalSequence (by simp) (by norm_num) 1 ψ,
      sourceGapWeightedEtaTerminalSequence (by simp) (by norm_num) (-1) ψ)

def sourceSignedTerminalFourier : CoeffPair 2 →L[ℂ] Coeff 2 :=
  Coeff.signedPositiveSplice.comp
    ((sourceGapWeightedEtaTerminalFourier 1).prod (sourceGapWeightedEtaTerminalFourier (-1)))

@[simp] theorem sourceSignedTerminalFourier_positive (h : CoeffPair 2) (k : ℤ) (hk : 0 < k) :
    sourceSignedTerminalFourier h k = -2*h.snd k := by
  change Coeff.signedPositiveSplice
    (sourceGapWeightedEtaTerminalFourier 1 h,sourceGapWeightedEtaTerminalFourier (-1) h) k = _
  rw [Coeff.signedPositiveSplice_positive _ _ k hk,sourceGapWeightedEtaTerminalFourier_apply]
  ring

@[simp] theorem sourceSignedTerminalFourier_negative (h : CoeffPair 2) (k : ℤ) (hk : k < 0) :
    sourceSignedTerminalFourier h k = -2*h.fst k := by
  change Coeff.signedPositiveSplice
    (sourceGapWeightedEtaTerminalFourier 1 h,sourceGapWeightedEtaTerminalFourier (-1) h) k = _
  rw [Coeff.signedPositiveSplice_negative _ _ k hk,sourceGapWeightedEtaTerminalFourier_apply,neg_neg]
  ring

@[simp] theorem sourceSignedTerminalSequence_zero (ψ : CoeffPair 2) :
    sourceSignedTerminalSequence ψ 0 = 0 := Coeff.signedPositiveSplice_zero _ _

/-- One complex neighborhood retains both selected literal terminals and
the actual compact derivative estimate in the full original L2 norm. -/
theorem exists_sourceSignedTerminalSequence_compact_derivative_domain :
    ∃ W : Set (CoeffPair 2), IsOpen W ∧ realTypeSourceLocus 2 ⊆ W ∧
      AnalyticOnNhd ℂ sourceSignedTerminalSequence W ∧ ∀ ψ ∈ W,
        (∀ k : ℤ, 0 < k → sourceSignedTerminalSequence ψ k =
          sourceGapWeightedEtaTerminalCoordinate (by simp) (by norm_num) k 1 ψ) ∧
        (∀ k : ℤ, k < 0 → sourceSignedTerminalSequence ψ k =
          sourceGapWeightedEtaTerminalCoordinate (by simp) (by norm_num) (-k) (-1) ψ) ∧
        IsCompactOperator (fderiv ℂ sourceSignedTerminalSequence ψ-sourceSignedTerminalFourier) := by
  obtain ⟨W,hW,hreal,hT⟩ := exists_gapWeightedEtaTerminalSequence_compact_derivative_domain
  have ha : AnalyticOnNhd ℂ sourceSignedTerminalSequence W := by
    intro ψ hψ
    exact ((Coeff.signedPositiveSplice (p := 2)).analyticAt _).comp
      (((hT 1).1 ψ hψ).prod ((hT (-1)).1 ψ hψ))
  refine ⟨W,hW,hreal,ha,fun ψ hψ => ⟨?_,?_,?_⟩⟩
  · intro k hk
    change Coeff.signedPositiveSplice _ k = _
    rw [Coeff.signedPositiveSplice_positive _ _ k hk]
    exact ((hT 1).2 ψ hψ).1 k
  · intro k hk
    change Coeff.signedPositiveSplice _ k = _
    rw [Coeff.signedPositiveSplice_negative _ _ k hk]
    exact ((hT (-1)).2 ψ hψ).1 (-k)
  · let P := Coeff.positiveFrequencyProjection (p := 2)
    let R := Coeff.reflection.toContinuousLinearEquiv.toContinuousLinearMap.comp P
    let A := fderiv ℂ (sourceGapWeightedEtaTerminalSequence (p := 2) (by simp) (by norm_num) 1) ψ
    let B := fderiv ℂ (sourceGapWeightedEtaTerminalSequence (p := 2) (by simp) (by norm_num) (-1)) ψ
    have hd : fderiv ℂ sourceSignedTerminalSequence ψ = Coeff.signedPositiveSplice.comp (A.prod B) :=
      ((Coeff.signedPositiveSplice (p := 2)).hasFDerivAt.comp ψ
        (((hT 1).1 ψ hψ).differentiableAt.hasFDerivAt.prodMk
          ((hT (-1)).1 ψ hψ).differentiableAt.hasFDerivAt)).fderiv
    have he : fderiv ℂ sourceSignedTerminalSequence ψ-sourceSignedTerminalFourier =
        P.comp (A-sourceGapWeightedEtaTerminalFourier 1)+
          R.comp (B-sourceGapWeightedEtaTerminalFourier (-1)) := by
      rw [hd]
      apply ContinuousLinearMap.ext
      intro h
      change P (A h)+R (B h)-(P (sourceGapWeightedEtaTerminalFourier 1 h)+
        R (sourceGapWeightedEtaTerminalFourier (-1) h)) =
          P (A h-sourceGapWeightedEtaTerminalFourier 1 h)+
            R (B h-sourceGapWeightedEtaTerminalFourier (-1) h)
      rw [map_sub,map_sub]
      abel
    rw [he]
    exact ((((hT 1).2 ψ hψ).2).clm_comp P).add
      ((((hT (-1)).2 ψ hψ).2).clm_comp R)

end NLS.ZakharovShabat
