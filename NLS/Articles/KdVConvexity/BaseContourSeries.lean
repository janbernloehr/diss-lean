import NLS.Articles.KdVConvexity.ActionEmbedding
import NLS.Articles.KdVConvexity.GlobalExtension

/-! # Restricting the weighted KdV contour series to Hilbert actions

Proposition 4.7(ii) starts with contour moments analytic on a neighborhood
of the positive ell^(-1,1) cone (Lemma 4.6(ii)). The actual continuous
inclusion constructed here pulls that domain back to ell2. Local quadratic
bounds then construct the analytic sum in the Hilbert norm.

The contour moments and their bounds are explicit hypotheses throughout.
No declaration in this file asserts their physical KdV existence.
-/
noncomputable section
set_option autoImplicit false
open Set
namespace NLS.Articles.KdVConvexity

/-- The exact weighted contour summand 8*n*pi*R_n in Proposition 4.7. -/
def weightedContourTerm (R : ℕ+ → BaseActionSpace → ℂ) (n : ℕ+) (b : BaseActionSpace) : ℂ :=
  ((8 * (n : ℝ) * Real.pi : ℝ) : ℂ) * R n b

/-- The weighted contour sum on the positive-index Hilbert action space. -/
def contourHamiltonian (R : ℕ+ → BaseActionSpace → ℂ) (a : ActionSpace) : ℂ :=
  ∑' n : ℕ+, weightedContourTerm R n (baseActionInclusion a)

/-- Analytic contour moments restrict analytically to the exact pulled-back
base neighborhood, with all weights in the physical normalization retained. -/
theorem analyticOnNhd_weightedContourTerm
    (R : ℕ+ → BaseActionSpace → ℂ) (U : Set BaseActionSpace)
    (hR : ∀ n, AnalyticOnNhd ℂ (R n) U) (n : ℕ+) :
    AnalyticOnNhd ℂ (fun a => weightedContourTerm R n (baseActionInclusion a))
      (baseActionInclusion ⁻¹' U) := by
  intro a ha
  exact (((hR n _ ha).comp (baseActionInclusion.analyticAt a)).const_smul
    (c := ((8 * (n : ℝ) * Real.pi : ℝ) : ℂ)))

/-- The analytic summation in Proposition 4.7(ii), on the exact preimage of
an open neighborhood in the source's ell^(-1,1) action space.

The input `hbound` is the locally uniform estimate
|8*n*pi*R_n(b)| <= C*|I_n(b)|^2 from the spectral analysis. It is required
around every base action, not just near the origin. -/
theorem analyticOnNhd_contourHamiltonian
    (R : ℕ+ → BaseActionSpace → ℂ) (U : Set BaseActionSpace) (hU : IsOpen U)
    (hR : ∀ n, AnalyticOnNhd ℂ (R n) U)
    (hbound : ∀ c ∈ U, ∃ T : Set BaseActionSpace, IsOpen T ∧ c ∈ T ∧ T ⊆ U ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ T, ∀ n : ℕ+,
        ‖weightedContourTerm R n b‖ ≤ C * ‖b.val (actionIndexEquiv.symm n)‖ ^ 2) :
    AnalyticOnNhd ℂ (contourHamiltonian R) (baseActionInclusion ⁻¹' U) := by
  apply analyticOnNhd_tsum_of_local_quadratic_bound
    (fun n a => weightedContourTerm R n (baseActionInclusion a))
    (baseActionInclusion ⁻¹' U) (hU.preimage baseActionInclusion.continuous)
    (analyticOnNhd_weightedContourTerm R U hR)
  intro a ha
  obtain ⟨T, hT, haT, hTU, C, hC, hb⟩ := hbound _ ha
  refine ⟨baseActionInclusion ⁻¹' T, hT.preimage baseActionInclusion.continuous,
    haT, fun b hb => hTU hb, C, hC, ?_⟩
  intro b hbT n
  simpa only [baseActionInclusion_apply, Equiv.apply_symm_apply] using
    hb (baseActionInclusion b) hbT n

/-- One complex open neighborhood containing all nonnegative ell2 actions,
with the contour Hamiltonian analytic there. This isolates the exact spectral
inputs still needed for the global extension clause of Theorem 1.1. -/
theorem global_analytic_contour_sum_from_base_moments
    (R : ℕ+ → BaseActionSpace → ℂ) (U : Set BaseActionSpace) (hU : IsOpen U)
    (hcone : WeightedCoeff.nonnegativeLocus baseActionWeight 1 ⊆ U)
    (hR : ∀ n, AnalyticOnNhd ℂ (R n) U)
    (hbound : ∀ c ∈ U, ∃ T : Set BaseActionSpace, IsOpen T ∧ c ∈ T ∧ T ⊆ U ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ T, ∀ n : ℕ+,
        ‖weightedContourTerm R n b‖ ≤ C * ‖b.val (actionIndexEquiv.symm n)‖ ^ 2) :
    IsOpen (baseActionInclusion ⁻¹' U) ∧
      positiveQuadrant ⊆ baseActionInclusion ⁻¹' U ∧
      AnalyticOnNhd ℂ (contourHamiltonian R) (baseActionInclusion ⁻¹' U) := by
  have hV := preimage_base_neighborhood U hU hcone
  exact ⟨hV.1, hV.2, analyticOnNhd_contourHamiltonian R U hU hR hbound⟩

end NLS.Articles.KdVConvexity
