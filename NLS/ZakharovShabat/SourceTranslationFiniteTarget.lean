import NLS.ZakharovShabat.SourceSpatialTranslation
import NLS.ZakharovShabat.NormalizedWeightedTruncation
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Analytic finite targets of the spatial translation curve

Finite Fourier truncation of the translation orbit has an entire complex
time extension even when the full source curve is only known continuous.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The finite weighted translation target at complex time. -/
def sourceTranslationFiniteTarget (w : SpectralWeight) (N : ℕ) (φ : CoeffPair p)
    (z : ℂ) : CoeffPair p :=
  WithLp.toLp p
    (∑ n ∈ Finset.Ioo (-(N : ℤ)) N,
      Complex.exp (z*((2*Real.pi*n : ℝ) : ℂ)*Complex.I) •
        lp.single p n ((w (2*n) : ℂ)*φ.fst n),
     ∑ n ∈ Finset.Ioo (-(N : ℤ)) N,
      Complex.exp (z*((2*Real.pi*n : ℝ) : ℂ)*Complex.I) •
        lp.single p n ((w (2*n) : ℂ)*φ.snd n))

/-- The finite target is entire as a map into the original Banach pair space. -/
theorem analyticAt_sourceTranslationFiniteTarget (w : SpectralWeight) (N : ℕ)
    (φ : CoeffPair p) (z : ℂ) : AnalyticAt ℂ (sourceTranslationFiniteTarget w N φ) z := by
  apply ((CoeffPair.toMax p).symm.analyticAt _).comp
  apply AnalyticAt.prod
  all_goals
    apply Finset.analyticAt_fun_sum
    intro n _
    exact (((analyticAt_id.mul analyticAt_const).mul analyticAt_const).cexp).smul analyticAt_const

/-- At real times this target is exactly the finite weighted block of the original translate. -/
theorem sourceTranslationFiniteTarget_ofReal (w : SpectralWeight) (N : ℕ)
    (φ : CoeffPair p) (t : ℝ) :
    sourceTranslationFiniteTarget w N φ t =
      normalizedWeightedTruncateCLM w N (sourceSpatialTranslation t φ) := by
  apply (CoeffPair.toMax p).injective
  apply Prod.ext <;> ext k
  all_goals
    change ((∑ n ∈ Finset.Ioo (-(N : ℤ)) N, _) : Coeff p) k = _
    simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      lp.single_apply, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq]
  · change (if k ∈ Finset.Ioo (-(N : ℤ)) N then _ else 0) =
      (normalizedWeightedTruncateCLM w N (sourceSpatialTranslation t φ)).fst k
    rw [normalizedWeightedTruncateCLM_fst, sourceSpatialTranslation_fst,
      Coeff.spatialTranslation_apply]
    split_ifs
    · push_cast
      ring
    · rfl
  · change (if k ∈ Finset.Ioo (-(N : ℤ)) N then _ else 0) =
      (normalizedWeightedTruncateCLM w N (sourceSpatialTranslation t φ)).snd k
    rw [normalizedWeightedTruncateCLM_snd, sourceSpatialTranslation_snd,
      Coeff.spatialTranslation_apply]
    split_ifs
    · push_cast
      ring
    · rfl

/-- The real-time finite target is real analytic, with no regularity assumption on the source. -/
theorem analyticAt_normalizedWeightedTruncate_translation (w : SpectralWeight) (N : ℕ)
    (φ : CoeffPair p) (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ => normalizedWeightedTruncateCLM w N
      (sourceSpatialTranslation s φ)) t := by
  have h := (analyticAt_sourceTranslationFiniteTarget w N φ (t : ℂ)).restrictScalars.comp
    (Complex.ofRealCLM.analyticAt t)
  change AnalyticAt ℝ (fun s : ℝ => sourceTranslationFiniteTarget w N φ (s : ℂ)) t at h
  simpa only [sourceTranslationFiniteTarget_ofReal] using h

end NLS.ZakharovShabat
