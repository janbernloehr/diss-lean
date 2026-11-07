import NLS.SequenceSpaces.SymmetricWeightedCompactTransfer
import NLS.SequenceSpaces.NonnegativeActionIdentity

/-! Cone-calibrated analytic frequency maps have intertwined FULL
corrected derivatives. Hessian symmetry then transfers actual weighted
ell1 compactness to the Hilbert action derivative at every boundary point. -/
noncomputable section
set_option autoImplicit false
open Set Filter Topology Complex
open scoped ENNReal
namespace NLS

theorem exists_open_common_clm_domain
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]
    (J : E →L[ℂ] F) (K : E →L[ℂ] G) (U : Set F) (V : Set G)
    (hU : IsOpen U) (hV : IsOpen V) (x : E) (hJx : J x∈U) (hKx : K x∈V) :
    ∃ W : Set E, IsOpen W ∧ x∈W ∧ (∀ y∈W, J y∈U) ∧ ∀ y∈W, K y∈V := by
  exact ⟨J ⁻¹' U∩K ⁻¹' V,(hU.preimage J.continuous).inter (hV.preimage K.continuous),
    ⟨hJx,hKx⟩,(fun _ hy => hy.1),(fun _ hy => hy.2)⟩

namespace Coeff

theorem isCompactOperator_corrected_hilbert_of_weighted_cone_agreement
    (J : Coeff 2 →L[ℂ] Coeff 1) (w : ℤ → ℝ) (hw : ∀ i, 0<w i)
    (hJ : ∀ x i, J x i=(w i : ℂ)*x i)
    (U : Set (Coeff 1)) (V W : Set (Coeff 2)) (hW : IsOpen W) (hWV : W⊆V)
    (hJU : ∀ x∈W, J x∈U) (F : Coeff 1 → Coeff 1) (H : Coeff 2 → Coeff 2)
    (hF : AnalyticOnNhd ℂ F U) (hH : AnalyticOnNhd ℂ H V)
    (x : Coeff 2) (hx : x∈W) (hxpos : x∈nonnegativeLocus 2) (c : ℂ)
    (he : ∀ y∈W, y∈nonnegativeLocus 2 → F (J y)=J (H y))
    (hsym : ∀ i j,
      (fderiv ℂ H x+c • ContinuousLinearMap.id ℂ (Coeff 2)) (lp.single 2 j 1) i=
        (fderiv ℂ H x+c • ContinuousLinearMap.id ℂ (Coeff 2)) (lp.single 2 i 1) j)
    (hc : IsCompactOperator (fderiv ℂ F (J x)+c • ContinuousLinearMap.id ℂ (Coeff 1))) :
    IsCompactOperator (fderiv ℂ H x+c • ContinuousLinearMap.id ℂ (Coeff 2)) := by
  have hFJ : AnalyticOnNhd ℂ (fun y => F (J y)) W :=
    fun y hy => (hF _ (hJU y hy)).comp (J.analyticAt y)
  have hJH : AnalyticOnNhd ℂ (fun y => J (H y)) W :=
    fun y hy => (J.analyticAt _).comp (hH y (hWV hy))
  have : Fact (1≤(4 : ℝ≥0∞)) := ⟨by norm_num⟩
  have : ENNReal.HolderTriple 4 4 2 := (ENNReal.holderTriple_iff _ _ _).mpr (by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_add])
  have heN := eventuallyEq_of_nonnegativeActions_agreement (p := 4) (q := 2) (by norm_num)
    (fun y => F (J y)) (fun y => J (H y)) W hW x hx hxpos hFJ.differentiableOn hJH.differentiableOn he
  have hdF := (hF _ (hJU x hx)).differentiableAt.hasFDerivAt.comp x J.hasFDerivAt
  have hdH := J.hasFDerivAt.comp x (hH x (hWV hx)).differentiableAt.hasFDerivAt
  have hd : (fderiv ℂ F (J x)).comp J=J.comp (fderiv ℂ H x) := by
    exact hdF.fderiv.symm.trans (heN.fderiv_eq.trans hdH.fderiv)
  let K := fderiv ℂ H x+c • ContinuousLinearMap.id ℂ (Coeff 2)
  let L := fderiv ℂ F (J x)+c • ContinuousLinearMap.id ℂ (Coeff 1)
  have hcorr : L.comp J=J.comp K := by
    apply ContinuousLinearMap.ext
    intro v
    change (fderiv ℂ F (J x)) (J v)+c • J v=J ((fderiv ℂ H x) v+c • v)
    rw [map_add,map_smul]
    exact congrArg (fun a : Coeff 1 => a+c • J v) (congrArg (fun A : Coeff 2 →L[ℂ] Coeff 1 => A v) hd)
  have hJsingle (j : ℤ) : J (lp.single 2 j 1)=(w j : ℂ) • lp.single 1 j 1 := by
    ext i
    rw [hJ]
    change (w i : ℂ)*(lp.single (E := fun _ : ℤ => ℂ) 2 j 1) i=(w j : ℂ)*(lp.single (E := fun _ : ℤ => ℂ) 1 j 1) i
    by_cases hi : i=j <;> simp [lp.single_apply,hi]
  apply isCompactOperator_symmetric_hilbert_of_weighted_one K L w hw hsym ?_ hc
  intro i j
  have hh := congrArg (fun A : Coeff 2 →L[ℂ] Coeff 1 => A (lp.single 2 j 1) i) hcorr
  change L (J (lp.single 2 j 1)) i=J (K (lp.single 2 j 1)) i at hh
  rw [hJsingle,map_smul,hJ] at hh
  have hn := congrArg norm hh
  change ‖(w j : ℂ)*(L (lp.single 1 j 1)) i‖=‖(w i : ℂ)*(K (lp.single 2 j 1)) i‖ at hn
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hw i),abs_of_pos (hw j)] at hn
  nlinarith only [hn]

end Coeff
end NLS
