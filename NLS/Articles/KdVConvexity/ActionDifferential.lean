import NLS.Articles.KdVConvexity.HilbertActionUnreindex
import NLS.SequenceSpaces.HilbertScalarGradient

/-! # The bilinear Hilbert gradient on the original positive-index action space -/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.Articles.KdVConvexity

theorem actionUnreindex_single (n : ℕ+) (c : ℂ) :
    actionUnreindex (lp.single 2 (actionIndexEquiv.symm n) c) = lp.single 2 n c := by
  ext m
  simp only [actionUnreindex_apply,lp.single_apply,Pi.single_apply,
    Equiv.symm_apply_eq,Equiv.apply_symm_apply]

/-- The continuous coefficient representation of a complex action cotangent.
The coefficients are bilinear, with no Hermitian conjugation of directions. -/
def actionCotangentCoefficients : (ActionSpace →L[ℂ] ℂ) →L[ℂ] ActionSpace :=
  actionUnreindex.toContinuousLinearMap.comp
    (Coeff.hilbertCotangentCoefficients.comp
      ((ContinuousLinearMap.compL ℂ (Coeff 2) ActionSpace ℂ).flip
        actionUnreindex.toContinuousLinearMap))

@[simp] theorem actionCotangentCoefficients_apply (L : ActionSpace →L[ℂ] ℂ) (n : ℕ+) :
    actionCotangentCoefficients L n = L (lp.single 2 n 1) := by
  change Coeff.hilbertCotangentCoefficients
    (L.comp actionUnreindex.toContinuousLinearMap) (actionIndexEquiv.symm n)=_
  rw [Coeff.hilbertCotangentCoefficients_apply]
  exact congrArg L (actionUnreindex_single n 1)

def actionGradient (H : ActionSpace → ℂ) (a : ActionSpace) : ActionSpace :=
  actionCotangentCoefficients (fderiv ℂ H a)

@[simp] theorem actionGradient_apply (H : ActionSpace → ℂ) (a : ActionSpace) (n : ℕ+) :
    actionGradient H a n = fderiv ℂ H a (lp.single 2 n 1) :=
  actionCotangentCoefficients_apply _ n

theorem analyticOnNhd_actionGradient (H : ActionSpace → ℂ) {V : Set ActionSpace}
    (hH : AnalyticOnNhd ℂ H V) : AnalyticOnNhd ℂ (actionGradient H) V := by
  intro a ha
  exact actionCotangentCoefficients.analyticAt _ |>.comp (hH.fderiv a ha)

/-- The Hilbert gradient represents the full differential, including infinite
directions. The literal positive-index series has the original coordinates. -/
theorem fderiv_eq_tsum_actionGradient (H : ActionSpace → ℂ) (a v : ActionSpace) :
    fderiv ℂ H a v = ∑' n : ℕ+, actionGradient H a n * v n := by
  have h := Coeff.dualPairing_hilbertCotangentCoefficients
    ((fderiv ℂ H a).comp actionUnreindex.toContinuousLinearMap) (actionReindex v)
  change Coeff.dualPairing (Coeff.hilbertCotangentCoefficients
    ((fderiv ℂ H a).comp actionUnreindex.toContinuousLinearMap)) (actionReindex v) =
      fderiv ℂ H a (actionUnreindex (actionReindex v)) at h
  rw [actionUnreindex_actionReindex] at h
  rw [Coeff.dualPairing_apply] at h
  apply h.symm.trans
  have he (k : ℤ) : Coeff.hilbertCotangentCoefficients
      ((fderiv ℂ H a).comp actionUnreindex.toContinuousLinearMap) k =
        actionGradient H a (actionIndexEquiv k) := by
    change _=Coeff.hilbertCotangentCoefficients
      ((fderiv ℂ H a).comp actionUnreindex.toContinuousLinearMap)
        (actionIndexEquiv.symm (actionIndexEquiv k))
    rw [Equiv.symm_apply_apply]
  simpa only [he,actionReindex_apply] using
    actionIndexEquiv.tsum_eq (fun n : ℕ+ => actionGradient H a n*v n)

end NLS.Articles.KdVConvexity
