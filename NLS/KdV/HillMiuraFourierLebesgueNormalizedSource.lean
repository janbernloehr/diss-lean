import NLS.KdV.HillMiuraSobolevNormalizedSource
import NLS.SequenceSpaces.PairExponentEmbedding

/-! # Literal native Fourier-Lebesgue coordinates of the actual Miura source

The period-one Dirichlet phase and half-scale spectral weight are kept
exactly. Exponent comparison changes none of the original coefficients.
-/
noncomputable section
set_option autoImplicit false
open Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.KdV
variable {p : ℝ≥0∞} [Fact (1≤p)]

def hillMiuraExponentDiagonal : Coeff p →L[ℂ] CoeffPair p := CoeffPair.inlCLM+CoeffPair.inrCLM

@[simp] theorem hillMiuraExponentDiagonal_fst (a : Coeff p) (n : ℤ) :
    (hillMiuraExponentDiagonal a).fst n=a n := by
  change (a+0 : Coeff p) n=a n
  rw [add_zero]

@[simp] theorem hillMiuraExponentDiagonal_snd (a : Coeff p) (n : ℤ) :
    (hillMiuraExponentDiagonal a).snd n=a n := by
  change (0+a : Coeff p) n=a n
  rw [zero_add]

def hillMiuraNormalizedFourierLebesgueDirichletSource (t : ℝ) :
    WeightedCoeff (Weight.sobolev t) p →L[ℂ] CoeffPair p :=
  sourcePhase.comp (hillMiuraExponentDiagonal.comp
    (WeightedCoeff.weightIsometry (Weight.sobolev t) p).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem hillMiuraNormalizedFourierLebesgueDirichletSource_fst
    (t : ℝ) (a : WeightedCoeff (Weight.sobolev t) p) (n : ℤ) :
    (hillMiuraNormalizedFourierLebesgueDirichletSource t a).fst n=
      I*((Weight.sobolev t n : ℂ)*a.val n) := by
  change (sourcePhase (hillMiuraExponentDiagonal (WeightedCoeff.weightEquiv (Weight.sobolev t) p a))).fst n=_
  rw [sourcePhase_fst]
  change I*(hillMiuraExponentDiagonal (WeightedCoeff.weightEquiv (Weight.sobolev t) p a)).fst n=_
  rw [hillMiuraExponentDiagonal_fst]
  rfl

@[simp] theorem hillMiuraNormalizedFourierLebesgueDirichletSource_snd
    (t : ℝ) (a : WeightedCoeff (Weight.sobolev t) p) (n : ℤ) :
    (hillMiuraNormalizedFourierLebesgueDirichletSource t a).snd n=
      -I*((Weight.sobolev t n : ℂ)*a.val n) := by
  change (sourcePhase (hillMiuraExponentDiagonal (WeightedCoeff.weightEquiv (Weight.sobolev t) p a))).snd n=_
  rw [sourcePhase_snd]
  change -I*(hillMiuraExponentDiagonal (WeightedCoeff.weightEquiv (Weight.sobolev t) p a)).snd n=_
  rw [hillMiuraExponentDiagonal_snd]
  rfl

theorem normalizedWeightedSource_hillMiuraFourierLebesgue
    (t : ℝ) (ht : 0≤t) (a : WeightedCoeff (Weight.sobolev t) p) (h2p : 2≤p)
    (u : Coeff 2) (hu : ∀ n : ℤ, a.val n=u n) :
    normalizedWeightedSource (sourceSobolevSpectralWeight t ht)
      (hillMiuraNormalizedFourierLebesgueDirichletSource t a)=
        CoeffPair.exponentInclusion h2p (sourcePhase (hillMiuraDiagonal u)) := by
  apply (CoeffPair.toMax p).injective
  apply Prod.ext
  · ext n
    change (normalizedWeightedSource _ _).fst n=(CoeffPair.exponentInclusion h2p _).fst n
    rw [normalizedWeightedSource_fst,hillMiuraNormalizedFourierLebesgueDirichletSource_fst,
      sourceSobolevSpectralWeight_even,CoeffPair.exponentInclusion_fst,
      Coeff.exponentInclusion_apply,sourcePhase_fst]
    simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,hillMiuraDiagonal_fst]
    change (I*((Weight.sobolev t n : ℂ)*a.val n))/(Weight.sobolev t n : ℂ)=I*u n
    rw [hu,mul_div_assoc,mul_div_cancel_left₀ _ (Weight.complex_ne_zero (Weight.sobolev t) n)]
  · ext n
    change (normalizedWeightedSource _ _).snd n=(CoeffPair.exponentInclusion h2p _).snd n
    rw [normalizedWeightedSource_snd,hillMiuraNormalizedFourierLebesgueDirichletSource_snd,
      sourceSobolevSpectralWeight_even,CoeffPair.exponentInclusion_snd,
      Coeff.exponentInclusion_apply,sourcePhase_snd]
    simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,hillMiuraDiagonal_snd]
    change (-I*((Weight.sobolev t n : ℂ)*a.val n))/(Weight.sobolev t n : ℂ)= -I*u n
    rw [hu,mul_div_assoc,mul_div_cancel_left₀ _ (Weight.complex_ne_zero (Weight.sobolev t) n)]

theorem isRealType_hillMiuraNormalizedFourierLebesgueDirichletSource
    (t : ℝ) (a : WeightedCoeff (Weight.sobolev t) p)
    (hr : ∀ n : ℤ, a.val (-n)=conj (a.val n)) :
    IsRealType (CoeffPair.toMax p (hillMiuraNormalizedFourierLebesgueDirichletSource t a)) := by
  intro n
  change (hillMiuraNormalizedFourierLebesgueDirichletSource t a).snd n=
    conj ((hillMiuraNormalizedFourierLebesgueDirichletSource t a).fst (-n))
  rw [hillMiuraNormalizedFourierLebesgueDirichletSource_snd,
    hillMiuraNormalizedFourierLebesgueDirichletSource_fst,hr,Weight.sobolev_neg]
  simp only [map_mul,conj_I,conj_ofReal,conj_conj]

end NLS.KdV
