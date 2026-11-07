import NLS.Articles.KdVConvexity.ActionHilbertGradientCoordinates
import NLS.SequenceSpaces.HilbertCompactActionIntertwining

/-! An actual analytic Hamiltonian gradient inherits corrected Hilbert
compactness from any calibrated compact weighted action realization.
The coordinate inclusion remains an abstract bounded linear map. -/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.Articles.KdVConvexity

theorem actionGradient_compact_of_weighted_cone_intertwining
    (H : ActionSpace → ℂ) (V : Set ActionSpace) (hV : IsOpen V) (hH : AnalyticOnNhd ℂ H V)
    (J : Coeff 2 →L[ℂ] Coeff 1) (w : ℤ → ℝ) (hw : ∀ i, 0<w i)
    (hJ : ∀ x i, J x i=(w i : ℂ)*x i)
    (hJpos : ∀ x∈Coeff.nonnegativeLocus 2, J x∈Coeff.nonnegativeLocus 1)
    (U : Set (Coeff 1)) (F : Coeff 1 → Coeff 1)
    (hU : IsOpen U) (hCU : Coeff.nonnegativeLocus 1⊆U) (hF : AnalyticOnNhd ℂ F U)
    (he : ∀ x∈Coeff.nonnegativeLocus 2, F (J x)=J (normalizedActionGradient H x))
    (hc : ∀ b∈Coeff.nonnegativeLocus 1,
      IsCompactOperator (fderiv ℂ F b+(6 : ℂ) • ContinuousLinearMap.id ℂ (Coeff 1)))
    (a : ActionSpace) (ha : a∈positiveQuadrant) (haV : a∈V) :
    IsCompactOperator (fderiv ℂ (actionGradient H) a+(6 : ℂ) • ContinuousLinearMap.id ℂ ActionSpace) := by
  let x := actionReindex a
  have hxpos : x∈Coeff.nonnegativeLocus 2 := fun k => ha (actionIndexEquiv k)
  have hxV : actionUnreindex x∈V := by
    rwa [show actionUnreindex x=a from actionUnreindex_actionReindex a]
  have hJx : J x∈Coeff.nonnegativeLocus 1 := hJpos x hxpos
  obtain ⟨W,hW,hxW,hJU,hWV⟩ := NLS.exists_open_common_clm_domain J actionUnreindex.toContinuousLinearMap
    U V hU hV x (hCU hJx) hxV
  apply isCompactOperator_actionGradient_of_normalized H a (hH a haV) 6
  exact Coeff.isCompactOperator_corrected_hilbert_of_weighted_cone_agreement
    J w hw hJ U (actionUnreindex ⁻¹' V) W hW (fun b hb => hWV b hb) hJU F (normalizedActionGradient H)
    hF (analyticOnNhd_normalizedActionGradient H V hH) x hxW hxpos 6
    (fun b _hb hbpos => he b hbpos)
    (normalizedActionGradient_corrected_matrix_symmetric H x (hH _ hxV) 6) (hc _ hJx)

end NLS.Articles.KdVConvexity
