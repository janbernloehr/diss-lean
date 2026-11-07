import NLS.Articles.KdVConvexity.ActionDifferentialSymmetry
import NLS.SequenceSpaces.CompactCorrectedDerivativeConjugate

/-! Exact Hilbert reindexing of the actual Hamiltonian gradient, its
symmetric corrected matrix and compact derivative. No coefficient weight
is introduced by the integer enumeration of positive action labels. -/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.Articles.KdVConvexity

def actionHilbertEquiv : ActionSpace ≃ₗᵢ[ℂ] Coeff 2 where
  toFun := actionReindex
  invFun := actionUnreindex
  left_inv := actionUnreindex_actionReindex
  right_inv := actionReindex_actionUnreindex
  map_add' := actionReindex.map_add
  map_smul' := actionReindex.map_smul
  norm_map' := actionReindex.norm_map

def normalizedActionGradient (H : ActionSpace → ℂ) (a : Coeff 2) : Coeff 2 :=
  actionReindex (actionGradient H (actionUnreindex a))

theorem analyticOnNhd_normalizedActionGradient (H : ActionSpace → ℂ)
    (V : Set ActionSpace) (hH : AnalyticOnNhd ℂ H V) :
    AnalyticOnNhd ℂ (normalizedActionGradient H) (actionUnreindex ⁻¹' V) := by
  intro a ha
  exact (actionReindex.toContinuousLinearMap.analyticAt _).comp
    ((analyticOnNhd_actionGradient H hH _ ha).comp (actionUnreindex.toContinuousLinearMap.analyticAt a))

theorem normalizedActionGradient_corrected_derivative (H : ActionSpace → ℂ)
    (a : Coeff 2) (hH : AnalyticAt ℂ H (actionUnreindex a)) (c : ℂ) :
    fderiv ℂ (normalizedActionGradient H) a+c • ContinuousLinearMap.id ℂ (Coeff 2)=
      actionReindex.toContinuousLinearMap.comp
        ((fderiv ℂ (actionGradient H) (actionUnreindex a)+c • ContinuousLinearMap.id ℂ ActionSpace).comp
          actionUnreindex.toContinuousLinearMap) := by
  have hg : DifferentiableAt ℂ (actionGradient H) (actionUnreindex a) :=
    (actionCotangentCoefficients.analyticAt _ |>.comp hH.fderiv).differentiableAt
  have hd := actionReindex.toContinuousLinearMap.hasFDerivAt.comp a
    (hg.hasFDerivAt.comp a actionUnreindex.toContinuousLinearMap.hasFDerivAt)
  change HasFDerivAt (normalizedActionGradient H)
    (actionReindex.toContinuousLinearMap.comp ((fderiv ℂ (actionGradient H) (actionUnreindex a)).comp
      actionUnreindex.toContinuousLinearMap)) a at hd
  rw [hd.fderiv]
  apply ContinuousLinearMap.ext
  intro v
  change actionReindex ((fderiv ℂ (actionGradient H) (actionUnreindex a)) (actionUnreindex v))+c • v=
    actionReindex ((fderiv ℂ (actionGradient H) (actionUnreindex a)) (actionUnreindex v)+c • actionUnreindex v)
  rw [map_add,map_smul,actionReindex_actionUnreindex]

theorem normalizedActionGradient_corrected_matrix_symmetric (H : ActionSpace → ℂ)
    (a : Coeff 2) (hH : AnalyticAt ℂ H (actionUnreindex a)) (c : ℂ) (i j : ℤ) :
    (fderiv ℂ (normalizedActionGradient H) a+c • ContinuousLinearMap.id ℂ (Coeff 2)) (lp.single 2 j 1) i=
      (fderiv ℂ (normalizedActionGradient H) a+c • ContinuousLinearMap.id ℂ (Coeff 2)) (lp.single 2 i 1) j := by
  rw [normalizedActionGradient_corrected_derivative H a hH c]
  have hs (k : ℤ) : actionUnreindex (lp.single 2 k 1)=lp.single 2 (actionIndexEquiv k) 1 := by
    simpa only [Equiv.symm_apply_apply] using actionUnreindex_single (actionIndexEquiv k) 1
  change (fderiv ℂ (actionGradient H) (actionUnreindex a)+c • ContinuousLinearMap.id ℂ ActionSpace)
    (actionUnreindex (lp.single 2 j 1)) (actionIndexEquiv i)=
      (fderiv ℂ (actionGradient H) (actionUnreindex a)+c • ContinuousLinearMap.id ℂ ActionSpace)
        (actionUnreindex (lp.single 2 i 1)) (actionIndexEquiv j)
  rw [hs j,hs i]
  exact actionGradient_corrected_matrix_symmetric H (actionUnreindex a) hH c _ _

theorem isCompactOperator_actionGradient_of_normalized (H : ActionSpace → ℂ)
    (a : ActionSpace) (hH : AnalyticAt ℂ H a) (c : ℂ)
    (hc : IsCompactOperator (fderiv ℂ (normalizedActionGradient H) (actionReindex a)+
      c • ContinuousLinearMap.id ℂ (Coeff 2))) :
    IsCompactOperator (fderiv ℂ (actionGradient H) a+c • ContinuousLinearMap.id ℂ ActionSpace) := by
  have hN : AnalyticAt ℂ (normalizedActionGradient H) (actionReindex a) := by
    apply (actionReindex.toContinuousLinearMap.analyticAt _).comp
    apply (actionCotangentCoefficients.analyticAt _ |>.comp ?_).comp
      (actionUnreindex.toContinuousLinearMap.analyticAt _)
    change AnalyticAt ℂ (fderiv ℂ H) (actionUnreindex (actionReindex a))
    rw [actionUnreindex_actionReindex]
    exact hH.fderiv
  have ht := NLS.isCompactOperator_corrected_fderiv_conjugate actionHilbertEquiv.symm.toContinuousLinearEquiv
    (normalizedActionGradient H) (actionReindex a) c hN.differentiableAt hc
  have he : (fun b : ActionSpace => actionUnreindex (normalizedActionGradient H (actionReindex b)))=actionGradient H := by
    funext b
    simp only [normalizedActionGradient,actionUnreindex_actionReindex]
  change IsCompactOperator (fderiv ℂ (fun b : ActionSpace => actionUnreindex (normalizedActionGradient H (actionReindex b)))
    (actionUnreindex (actionReindex a))+c • ContinuousLinearMap.id ℂ ActionSpace) at ht
  rwa [he,actionUnreindex_actionReindex] at ht

end NLS.Articles.KdVConvexity
