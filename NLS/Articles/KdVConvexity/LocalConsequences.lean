import NLS.SequenceSpaces.HilbertStrictConcavity
import NLS.SequenceSpaces.HilbertMatrixTranspose
import NLS.SequenceSpaces.OperatorBasisExt
import NLS.ComplexAnalysis.AnalyticOpenInverse

/-! # Analytic consequences of the KdV Hessian normalization

Preparation for Theorem 1.1 of arXiv:1502.05857v1, pp. 3–4.
These are conditional analytic lemmas, not a construction of the KdV
Hamiltonian. `Coeff 2` is indexed by integers; a future article interface must
identify this model with the paper's positive-index action space.
-/
noncomputable section
set_option autoImplicit false
open Set Metric
namespace NLS.Articles.KdVConvexity

/-- Scalar rescaling commutes with the bilinear Hilbert gradient. -/
theorem scalarGradient_const_smul (c : ℂ) (H : Coeff 2 → ℂ) :
    Coeff.scalarGradient (c • H) = c • Coeff.scalarGradient H := by
  funext b
  simp only [Coeff.scalarGradient, fderiv_const_smul_field, Pi.smul_apply, map_smul]

/-- Once the scalar function is analytic on Hilbert space, its basis Hessian
entries determine the full bounded gradient derivative, including directions
with infinite support. This is the analytic step from (1.5) to an operator
identity; it does not establish the KdV Taylor coefficients themselves. -/
theorem gradient_derivative_of_basis_hessian
    (H : Coeff 2 → ℂ) (hH : AnalyticAt ℂ H 0) (c : ℂ)
    (hess : ∀ k n : ℤ,
      fderiv ℂ (fderiv ℂ H) 0 (lp.single 2 k 1) (lp.single 2 n 1) =
        if k = n then c else 0) :
    fderiv ℂ (Coeff.scalarGradient H) 0 =
      c • ContinuousLinearMap.id ℂ (Coeff 2) := by
  apply Coeff.continuousLinearMap_eq_of_single (by norm_num)
  intro k
  ext n
  have hn := hess k n
  rw [Coeff.hessian_eq_dualPairing_gradient_derivative H 0 hH,
    Coeff.dualPairing_hilbert_single_right] at hn
  change (fderiv ℂ (Coeff.scalarGradient H) 0 (lp.single 2 k 1)) n = _
  rw [hn]
  simp only [smul_apply, ContinuousLinearMap.id_apply, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul, lp.single_apply]
  by_cases hnk : n = k
  · subst n
    simp
  · simp [hnk, Ne.symm hnk]

/-- The existing minus-two concavity argument also applies to the KdV
minus-six normalization, by rescaling the scalar function by one third.
The resulting estimate is stronger than (1.8). -/
theorem exists_ball_hessian_le_neg_three_norm_sq
    (H : Coeff 2 → ℂ) (V : Set (Coeff 2)) (hV : IsOpen V)
    (h0 : (0 : Coeff 2) ∈ V) (hH : AnalyticOnNhd ℂ H V)
    (hd0 : fderiv ℂ (Coeff.scalarGradient H) 0 =
      (-6 : ℂ) • ContinuousLinearMap.id ℂ (Coeff 2)) :
    ∃ r : ℝ, 0 < r ∧ ball (0 : Coeff 2) r ⊆ V ∧
      ∀ b ∈ ball (0 : Coeff 2) r, ∀ J : RealCoeff 2,
        (fderiv ℂ (fderiv ℂ H) b (RealCoeff.complexCLM 2 J)
          (RealCoeff.complexCLM 2 J)).re ≤ -3 * ‖J‖ ^ 2 := by
  let K : Coeff 2 → ℂ := (1 / 3 : ℂ) • H
  have hK : AnalyticOnNhd ℂ K V := by
    intro b hb
    exact (hH b hb).const_smul (c := (1 / 3 : ℂ))
  have hdK : fderiv ℂ (Coeff.scalarGradient K) 0 =
      (-2 : ℂ) • ContinuousLinearMap.id ℂ (Coeff 2) := by
    rw [show Coeff.scalarGradient K = (1 / 3 : ℂ) • Coeff.scalarGradient H from
      scalarGradient_const_smul _ _, fderiv_const_smul_field, Pi.smul_apply, hd0,
      smul_smul]
    norm_num
  obtain ⟨r, hr, hball, hess⟩ :=
    Coeff.exists_ball_hessian_le_negative_norm_sq K V hV h0 hK hdK
  refine ⟨r, hr, hball, ?_⟩
  intro b hb J
  have he : fderiv ℂ (fderiv ℂ K) = (1 / 3 : ℂ) • fderiv ℂ (fderiv ℂ H) := by
    change fderiv ℂ (fderiv ℂ ((1 / 3 : ℂ) • H)) = _
    rw [fderiv_const_smul_field]
    exact fderiv_const_smul_field (𝕜 := ℂ) (f := fderiv ℂ H) (1 / 3 : ℂ)
  have h := hess b hb J
  rw [he] at h
  simp only [Pi.smul_apply, smul_apply, smul_eq_mul,
    Complex.mul_re] at h
  norm_num at h
  linarith

/-- The quantitative bound of equation (1.8) and literal strict concavity
hold on one common neighborhood. All KdV-specific input remains explicit. -/
theorem local_concavity_of_derivative_neg_six
    (H : Coeff 2 → ℂ) (V : Set (Coeff 2)) (hV : IsOpen V)
    (h0 : (0 : Coeff 2) ∈ V) (hH : AnalyticOnNhd ℂ H V)
    (hd0 : fderiv ℂ (Coeff.scalarGradient H) 0 =
      (-6 : ℂ) • ContinuousLinearMap.id ℂ (Coeff 2)) :
    ∃ r : ℝ, 0 < r ∧ ball (0 : Coeff 2) r ⊆ V ∧
      (∀ b ∈ ball (0 : Coeff 2) r, ∀ J : RealCoeff 2,
        (fderiv ℂ (fderiv ℂ H) b (RealCoeff.complexCLM 2 J)
          (RealCoeff.complexCLM 2 J)).re ≤ -‖J‖ ^ 2) ∧
      StrictConcaveOn ℝ (ball (0 : Coeff 2) r ∩ Coeff.nonnegativeLocus 2)
        (fun b => (H b).re) := by
  obtain ⟨r, hr, hball, hstrong⟩ :=
    exists_ball_hessian_le_neg_three_norm_sq H V hV h0 hH hd0
  have hess : ∀ b ∈ ball (0 : Coeff 2) r, ∀ J : RealCoeff 2,
      (fderiv ℂ (fderiv ℂ H) b (RealCoeff.complexCLM 2 J)
        (RealCoeff.complexCLM 2 J)).re ≤ -‖J‖ ^ 2 := by
    intro b hb J
    have h := hstrong b hb J
    nlinarith [sq_nonneg ‖J‖]
  refine ⟨r, hr, hball, hess, ?_⟩
  apply (Coeff.strictConcaveOn_real_hilbert_ball H V hV hH r hball hess).subset
    (fun b hb => ⟨hb.1, fun n => (hb.2 n).1⟩)
  exact (convex_ball (0 : Coeff 2) r).inter (Coeff.convex_nonnegativeLocus 2)

/-- Any analytic map with KdV's derivative at zero admits an analytic inverse
on actual open neighborhoods; this works directly for positive-index ell2. -/
theorem local_open_inverse_of_derivative_neg_six
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {F : E → E} {U : Set E} (hU : IsOpen U) (hF : AnalyticOnNhd ℂ F U)
    (h0 : (0 : E) ∈ U) (hF0 : F 0 = 0)
    (hd0 : fderiv ℂ F 0 = (-6 : ℂ) • ContinuousLinearMap.id ℂ E) :
    ∃ V W : Set E, IsOpen V ∧ IsOpen W ∧ (0 : E) ∈ V ∧ (0 : E) ∈ W ∧
      V ⊆ U ∧ F '' V = W ∧ Set.BijOn F V W ∧
      ∃ G : E → E, AnalyticOnNhd ℂ F V ∧ AnalyticOnNhd ℂ G W ∧
        (∀ b ∈ V, G (F b) = b) ∧ (∀ c ∈ W, G c ∈ V ∧ F (G c) = c) := by
  have hu : IsUnit (fderiv ℂ F 0) := by
    rw [hd0, ContinuousLinearMap.isUnit_iff_bijective]
    exact (LinearEquiv.smulOfNeZero ℂ E (-6) (by norm_num)).bijective
  simpa only [hF0] using
    NLS.ComplexAnalysis.exists_analytic_inverse_open_sets hU hF h0 hu

end NLS.Articles.KdVConvexity
