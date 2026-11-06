import NLS.Articles.KdVConvexity.TailExtension
import NLS.Articles.KdVConvexity.BaseContourSeries

noncomputable section
set_option autoImplicit false
open Set
namespace NLS.Articles.KdVConvexity

theorem global_analytic_contour_sum_from_base_tail_bounds
    (R : ℕ+ → BaseActionSpace → ℂ) (U : Set BaseActionSpace) (hU : IsOpen U)
    (hcone : WeightedCoeff.nonnegativeLocus baseActionWeight 1 ⊆ U)
    (hR : ∀ n, AnalyticOnNhd ℂ (R n) U)
    (hbound : ∀ c ∈ U, ∃ T : Set BaseActionSpace, IsOpen T ∧ c ∈ T ∧ T ⊆ U ∧
      ∃ s : Finset ℕ+, ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ T, ∀ n ∉ s,
        ‖weightedContourTerm R n b‖ ≤ C * ‖b.val (actionIndexEquiv.symm n)‖ ^ 2) :
    IsOpen (baseActionInclusion ⁻¹' U) ∧
      positiveQuadrant ⊆ baseActionInclusion ⁻¹' U ∧
      AnalyticOnNhd ℂ (contourHamiltonian R) (baseActionInclusion ⁻¹' U) ∧
      ∀ a ∈ baseActionInclusion ⁻¹' U,
        Summable (fun n => ‖weightedContourTerm R n (baseActionInclusion a)‖) := by
  have hV := preimage_base_neighborhood U hU hcone
  have hlocal (a : ActionSpace) (ha : a ∈ baseActionInclusion ⁻¹' U) :
      ∃ T : Set ActionSpace, IsOpen T ∧ a ∈ T ∧ T ⊆ baseActionInclusion ⁻¹' U ∧
        ∃ s : Finset ℕ+, ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ T, ∀ n ∉ s,
          ‖weightedContourTerm R n (baseActionInclusion b)‖ ≤ C * ‖b n‖ ^ 2 := by
    obtain ⟨T,hT,haT,hTU,s,C,hC,hb⟩ := hbound _ ha
    refine ⟨baseActionInclusion ⁻¹' T,hT.preimage baseActionInclusion.continuous,
      haT,fun _ hb => hTU hb,s,C,hC,?_⟩
    intro b hbT n hn
    simpa only [baseActionInclusion_apply,Equiv.apply_symm_apply] using
      hb (baseActionInclusion b) hbT n hn
  refine ⟨hV.1,hV.2,?_,?_⟩
  · intro a ha
    obtain ⟨T,hT,haT,hTU,s,C,hC,hb⟩ := hlocal a ha
    exact analyticOnNhd_tsum_of_tail_quadratic_bound
      (fun n a => weightedContourTerm R n (baseActionInclusion a)) T hT
      (fun n => (analyticOnNhd_weightedContourTerm R U hR n).mono hTU)
      s C hC hb a haT
  · intro a ha
    obtain ⟨T,_,haT,_,s,C,hC,hb⟩ := hlocal a ha
    exact summable_norm_of_tail_quadratic_bound
      (fun n a => weightedContourTerm R n (baseActionInclusion a)) s a C hC (hb a haT)

end NLS.Articles.KdVConvexity
