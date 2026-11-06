import NLS.KdV.MiuraDirichletSourcePhase
import NLS.KdV.MiuraCanonicalRootReflection
import NLS.ZakharovShabat.SourceSection14WeightedMembership
import NLS.SequenceSpaces.SobolevHomogeneous
import NLS.SequenceSpaces.PeriodOneMiuraConjugation

/-! # Exact native Sobolev coordinates of the actual Dirichlet Miura source

The source-frequency weight is evaluated at the correct even spectral
index. Decoding the normalized native source therefore gives EXACTLY the
phase-rotated actual Miura lift, with its original raw coefficients.
-/
noncomputable section
set_option autoImplicit false
open Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.KdV

/-- The actual ordinary Dirichlet source in normalized H^t coordinates. -/
def hillMiuraNormalizedSobolevDirichletSource (t : ℝ) :
    WeightedCoeff (Weight.sobolev t) 2 →L[ℂ] CoeffPair 2 :=
  sourcePhase.comp (hillMiuraDiagonal.comp
    (WeightedCoeff.weightIsometry (Weight.sobolev t) 2).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem hillMiuraNormalizedSobolevDirichletSource_fst
    (t : ℝ) (a : WeightedCoeff (Weight.sobolev t) 2) (n : ℤ) :
    (hillMiuraNormalizedSobolevDirichletSource t a).fst n=
      I*((Weight.sobolev t n : ℂ)*a.val n) := by
  change (sourcePhase (hillMiuraDiagonal (WeightedCoeff.weightEquiv (Weight.sobolev t) 2 a))).fst n=_
  rw [sourcePhase_fst,hillMiuraDiagonal_fst]
  rfl

@[simp] theorem hillMiuraNormalizedSobolevDirichletSource_snd
    (t : ℝ) (a : WeightedCoeff (Weight.sobolev t) 2) (n : ℤ) :
    (hillMiuraNormalizedSobolevDirichletSource t a).snd n=
      -I*((Weight.sobolev t n : ℂ)*a.val n) := by
  change (sourcePhase (hillMiuraDiagonal (WeightedCoeff.weightEquiv (Weight.sobolev t) 2 a))).snd n=_
  rw [sourcePhase_snd,hillMiuraDiagonal_snd]
  rfl

/-- The half-scale spectral normalization preserves the actual period-one
source and its ordinary Dirichlet phase, at EVERY nonnegative real order. -/
theorem normalizedWeightedSource_hillMiuraSobolev
    (t : ℝ) (ht : 0≤t) (a : WeightedCoeff (Weight.sobolev t) 2) :
    normalizedWeightedSource (sourceSobolevSpectralWeight t ht)
      (hillMiuraNormalizedSobolevDirichletSource t a)=
        sourcePhase (hillMiuraDiagonal (WeightedCoeff.sobolevToL2 ht a)) := by
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext
  · ext n
    change (normalizedWeightedSource _ _).fst n=(sourcePhase _).fst n
    rw [normalizedWeightedSource_fst,hillMiuraNormalizedSobolevDirichletSource_fst,
      sourceSobolevSpectralWeight_even,sourcePhase_fst,hillMiuraDiagonal_fst]
    change (I*((Weight.sobolev t n : ℂ)*a.val n))/(Weight.sobolev t n : ℂ)=
      I*(WeightedCoeff.sobolevToL2 ht a n)
    rw [WeightedCoeff.sobolevToL2_apply,mul_div_assoc,
      mul_div_cancel_left₀ _ (Weight.complex_ne_zero (Weight.sobolev t) n)]
  · ext n
    change (normalizedWeightedSource _ _).snd n=(sourcePhase _).snd n
    rw [normalizedWeightedSource_snd,hillMiuraNormalizedSobolevDirichletSource_snd,
      sourceSobolevSpectralWeight_even,sourcePhase_snd,hillMiuraDiagonal_snd]
    change (-I*((Weight.sobolev t n : ℂ)*a.val n))/(Weight.sobolev t n : ℂ)=
      -I*(WeightedCoeff.sobolevToL2 ht a n)
    rw [WeightedCoeff.sobolevToL2_apply,mul_div_assoc,
      mul_div_cancel_left₀ _ (Weight.complex_ne_zero (Weight.sobolev t) n)]

/-- Normalized native coordinates preserve the original physical real
form of the actual Miura lift. -/
theorem isRealType_hillMiuraNormalizedSobolevDirichletSource
    (t : ℝ) (ht : 0≤t) (a : WeightedCoeff (Weight.sobolev t) 2)
    (hr : periodOneL2Conjugation (WeightedCoeff.sobolevToL2 ht a)=WeightedCoeff.sobolevToL2 ht a) :
    IsRealType (CoeffPair.toMax 2 (hillMiuraNormalizedSobolevDirichletSource t a)) := by
  have ha (n : ℤ) : a.val (-n)=conj (a.val n) := by
    simpa only [WeightedCoeff.sobolevToL2_apply] using
      (periodOneL2Conjugation_fixed_iff _).mp hr n
  have hw (n : ℤ) :
      WeightedCoeff.weightEquiv (Weight.sobolev t) 2 a (-n)=
        conj (WeightedCoeff.weightEquiv (Weight.sobolev t) 2 a n) := by
    simp only [WeightedCoeff.weightEquiv_apply,Weight.sobolev_neg,map_mul,Complex.conj_ofReal,ha n]
  exact isRealType_sourcePhase _ (isRealType_hillMiuraDiagonal ⟨_,hw⟩)

end NLS.KdV
