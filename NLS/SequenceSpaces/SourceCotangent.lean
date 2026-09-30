import NLS.SequenceSpaces.HilbertCotangent
import NLS.SequenceSpaces.PairExponentEmbedding

/-! # Square-summable Fourier coefficients of source cotangents

The two component injections preserve the dissertation's source norm.
Restriction of a source cotangent to each component's Hilbert directions
therefore gives square-summable Fourier coefficients, bounded by the
original operator norm, and depending continuously and linearly on it.
-/

noncomputable section
open scoped ENNReal
namespace NLS.CoeffPair
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def inlCLM : Coeff p →L[ℂ] CoeffPair p :=
  ((toMax p).symm.toContinuousLinearMap).comp (ContinuousLinearMap.inl ℂ (Coeff p) (Coeff p))

def inrCLM : Coeff p →L[ℂ] CoeffPair p :=
  ((toMax p).symm.toContinuousLinearMap).comp (ContinuousLinearMap.inr ℂ (Coeff p) (Coeff p))

@[simp] theorem inlCLM_fst (a : Coeff p) : (inlCLM a).fst = a := rfl
@[simp] theorem inlCLM_snd (a : Coeff p) : (inlCLM a).snd = 0 := rfl
@[simp] theorem inrCLM_fst (a : Coeff p) : (inrCLM a).fst = 0 := rfl
@[simp] theorem inrCLM_snd (a : Coeff p) : (inrCLM a).snd = a := rfl

@[simp] theorem norm_inlCLM (a : Coeff p) : ‖inlCLM a‖ = ‖a‖ :=
  WithLp.norm_toLp_fst p _ _ a

@[simp] theorem norm_inrCLM (a : Coeff p) : ‖inrCLM a‖ = ‖a‖ :=
  WithLp.norm_toLp_snd p _ _ a

/-- Cotangent Fourier coefficients. Physical gradient coefficients reverse
the frequency index because the differential uses bilinear L² duality. -/
def cotangentCoefficients (h2p : (2:ℝ≥0∞) ≤ p) :
    (CoeffPair p →L[ℂ] ℂ) →L[ℂ] (Coeff 2 × Coeff 2) :=
  ((Coeff.hilbertCotangentRestriction h2p).comp
    ((ContinuousLinearMap.compL ℂ (Coeff p) (CoeffPair p) ℂ).flip inlCLM)).prod
  ((Coeff.hilbertCotangentRestriction h2p).comp
    ((ContinuousLinearMap.compL ℂ (Coeff p) (CoeffPair p) ℂ).flip inrCLM))

@[simp] theorem cotangentCoefficients_fst (h2p : (2:ℝ≥0∞) ≤ p)
    (L : CoeffPair p →L[ℂ] ℂ) (n : ℤ) :
    (cotangentCoefficients h2p L).1 n = L (inlCLM (lp.single p n 1)) :=
  Coeff.hilbertCotangentRestriction_apply h2p (L.comp inlCLM) n

@[simp] theorem cotangentCoefficients_snd (h2p : (2:ℝ≥0∞) ≤ p)
    (L : CoeffPair p →L[ℂ] ℂ) (n : ℤ) :
    (cotangentCoefficients h2p L).2 n = L (inrCLM (lp.single p n 1)) :=
  Coeff.hilbertCotangentRestriction_apply h2p (L.comp inrCLM) n

theorem norm_cotangentCoefficients_le (h2p : (2:ℝ≥0∞) ≤ p) (L : CoeffPair p →L[ℂ] ℂ) :
    ‖cotangentCoefficients h2p L‖ ≤ ‖L‖ := by
  have hleft : ‖L.comp inlCLM‖ ≤ ‖L‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro a
    simpa only [ContinuousLinearMap.comp_apply,norm_inlCLM] using L.le_opNorm (inlCLM a)
  have hright : ‖L.comp inrCLM‖ ≤ ‖L‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro a
    simpa only [ContinuousLinearMap.comp_apply,norm_inrCLM] using L.le_opNorm (inrCLM a)
  exact max_le ((Coeff.norm_hilbertCotangentRestriction_le h2p _).trans hleft)
    ((Coeff.norm_hilbertCotangentRestriction_le h2p _).trans hright)

/-- Both component coefficient sequences recover the original source
cotangent on the entire Hilbert source space. -/
theorem dualPairing_cotangentCoefficients (h2p : (2:ℝ≥0∞) ≤ p)
    (L : CoeffPair p →L[ℂ] ℂ) (h : CoeffPair 2) :
    Coeff.dualPairing (cotangentCoefficients h2p L).1 h.fst +
      Coeff.dualPairing (cotangentCoefficients h2p L).2 h.snd =
        L (exponentInclusion h2p h) := by
  change Coeff.dualPairing (Coeff.hilbertCotangentRestriction h2p (L.comp inlCLM)) h.fst +
    Coeff.dualPairing (Coeff.hilbertCotangentRestriction h2p (L.comp inrCLM)) h.snd = _
  rw [Coeff.dualPairing_hilbertCotangentRestriction,
    Coeff.dualPairing_hilbertCotangentRestriction]
  change L (inlCLM (Coeff.exponentInclusion h2p h.fst)) +
    L (inrCLM (Coeff.exponentInclusion h2p h.snd)) = _
  rw [← map_add]
  congr 1
  apply (toMax p).injective
  apply Prod.ext <;> simp

end NLS.CoeffPair
