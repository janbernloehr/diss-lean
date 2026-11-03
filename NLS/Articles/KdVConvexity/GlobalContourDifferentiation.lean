import NLS.Articles.KdVConvexity.BaseContourSeries
import NLS.Articles.KdVConvexity.TailSeriesRealization

/-! # The global ell2 contour extension as an analytic ell1 family

The same pulled-back base-action neighborhood carries the entire weighted
contour sequence, its absolutely convergent sum and termwise directional
derivatives. The local spectral cutoff is chosen before all high indices
and all complex actions in its patch. Physical action and energy
identifications remain separate obligations.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace NLS.Articles.KdVConvexity

/-- The complete sequence of actual weighted summands, including the head. -/
def contourTermFamily (R : ℕ+ → BaseActionSpace → ℂ) : ActionSpace → Coeff 1 :=
  seriesTerms (fun n a => weightedContourTerm R n (baseActionInclusion a))

theorem preimage_subset_globalTailSeriesDomain_of_base_tail_bounds
    (R : ℕ+ → BaseActionSpace → ℂ) (U : Set BaseActionSpace) (_hU : IsOpen U)
    (hR : ∀ n, AnalyticOnNhd ℂ (R n) U)
    (hbound : ∀ c ∈ U, ∃ T : Set BaseActionSpace, IsOpen T ∧ c ∈ T ∧ T ⊆ U ∧
      ∃ s : Finset ℕ+, ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ T, ∀ n ∉ s,
        ‖weightedContourTerm R n b‖ ≤ C*‖b.val (actionIndexEquiv.symm n)‖^2) :
    baseActionInclusion ⁻¹' U ⊆
      globalTailSeriesDomain (fun n a => weightedContourTerm R n (baseActionInclusion a)) := by
  intro a ha
  obtain ⟨T,hT,haT,hTU,s,C,hC,hb⟩ := hbound _ ha
  refine mem_sUnion.mpr ⟨baseActionInclusion ⁻¹' T,⟨hT.preimage baseActionInclusion.continuous,
    fun n => (analyticOnNhd_weightedContourTerm R U hR n).mono (fun _ hb => hTU hb),
    s,C,hC,?_⟩,haT⟩
  intro b hbT n hn
  simpa only [baseActionInclusion_apply,Equiv.apply_symm_apply] using
    hb (baseActionInclusion b) hbT n hn

/-- On exactly the same global domain, all weighted contour terms form
one Banach-analytic ell1 map. No common cutoff for the whole cone is used. -/
theorem global_analytic_contour_family_from_base_tail_bounds
    (R : ℕ+ → BaseActionSpace → ℂ) (U : Set BaseActionSpace) (hU : IsOpen U)
    (hcone : WeightedCoeff.nonnegativeLocus baseActionWeight 1 ⊆ U)
    (hR : ∀ n, AnalyticOnNhd ℂ (R n) U)
    (hbound : ∀ c ∈ U, ∃ T : Set BaseActionSpace, IsOpen T ∧ c ∈ T ∧ T ⊆ U ∧
      ∃ s : Finset ℕ+, ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ T, ∀ n ∉ s,
        ‖weightedContourTerm R n b‖ ≤ C*‖b.val (actionIndexEquiv.symm n)‖^2) :
    IsOpen (baseActionInclusion ⁻¹' U) ∧ positiveQuadrant ⊆ baseActionInclusion ⁻¹' U ∧
      AnalyticOnNhd ℂ (contourTermFamily R) (baseActionInclusion ⁻¹' U) ∧
      (∀ a ∈ baseActionInclusion ⁻¹' U, ∀ k : ℤ,
        contourTermFamily R a k = weightedContourTerm R (actionIndexEquiv k) (baseActionInclusion a)) ∧
      (∀ a ∈ baseActionInclusion ⁻¹' U,
        contourHamiltonian R a = lp.tsumCLM ℂ ℤ ℂ (contourTermFamily R a)) ∧
      ∀ a ∈ baseActionInclusion ⁻¹' U, ∀ v : ActionSpace,
        Summable (fun n => ‖fderiv ℂ (fun b => weightedContourTerm R n (baseActionInclusion b)) a v‖) ∧
          fderiv ℂ (contourHamiltonian R) a v =
            ∑' n, fderiv ℂ (fun b => weightedContourTerm R n (baseActionInclusion b)) a v := by
  let M : ℕ+ → ActionSpace → ℂ := fun n a => weightedContourTerm R n (baseActionInclusion a)
  have hsub := preimage_subset_globalTailSeriesDomain_of_base_tail_bounds R U hU hR hbound
  have hV := preimage_base_neighborhood U hU hcone
  have hs (a : ActionSpace) (ha : a ∈ baseActionInclusion ⁻¹' U) :=
    (analytic_summable_globalTailSeriesDomain M).2 a (hsub ha)
  refine ⟨hV.1,hV.2,(analyticOnNhd_seriesTerms_globalTailSeriesDomain M).mono hsub,
    fun a ha k => seriesTerms_apply_of_summable M a (hs a ha) k,?_,?_⟩
  · intro a ha
    change (∑' n, M n a) = ∑' k : ℤ, seriesTerms M a k
    simp only [seriesTerms_apply_of_summable M a (hs a ha)]
    exact (actionIndexEquiv.tsum_eq (fun n => M n a)).symm
  · intro a ha v
    exact fderiv_tsum_eq_tsum_fderiv_of_mem_globalTailSeriesDomain M a (hsub ha) v

/-- The full contour sums converge uniformly on every compact subset of
the same complex ell2 neighborhood, including all finite head terms. -/
theorem contour_sums_tendstoUniformlyOn_of_base_tail_bounds
    (R : ℕ+ → BaseActionSpace → ℂ) (U : Set BaseActionSpace) (hU : IsOpen U)
    (hR : ∀ n, AnalyticOnNhd ℂ (R n) U)
    (hbound : ∀ c ∈ U, ∃ T : Set BaseActionSpace, IsOpen T ∧ c ∈ T ∧ T ⊆ U ∧
      ∃ s : Finset ℕ+, ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ T, ∀ n ∉ s,
        ‖weightedContourTerm R n b‖ ≤ C*‖b.val (actionIndexEquiv.symm n)‖^2)
    (K : Set ActionSpace) (hK : IsCompact K) (hKU : K ⊆ baseActionInclusion ⁻¹' U) :
    TendstoUniformlyOn
      (fun (N : ℕ) a => ∑ k ∈ Finset.Icc (-(N : ℤ)) N,
        weightedContourTerm R (actionIndexEquiv k) (baseActionInclusion a))
      (contourHamiltonian R) atTop K := by
  let M : ℕ+ → ActionSpace → ℂ := fun n a => weightedContourTerm R n (baseActionInclusion a)
  have hsub := preimage_subset_globalTailSeriesDomain_of_base_tail_bounds R U hU hR hbound
  have hf := ((analyticOnNhd_seriesTerms_globalTailSeriesDomain M).mono (hKU.trans hsub)).continuousOn
  have hlim := Coeff.tendstoUniformlyOn_sums_of_isCompact (seriesTerms M) K hK hf
  have he (a : ActionSpace) (ha : a ∈ K) (k : ℤ) : seriesTerms M a k = M (actionIndexEquiv k) a :=
    seriesTerms_apply_of_summable M a
      ((analytic_summable_globalTailSeriesDomain M).2 a (hsub (hKU ha))) k
  have htarget : EqOn (fun a => ∑' k : ℤ, seriesTerms M a k) (contourHamiltonian R) K := by
    intro a ha
    change (∑' k : ℤ, seriesTerms M a k) = ∑' n, M n a
    simp only [he a ha]
    exact actionIndexEquiv.tsum_eq (fun n => M n a)
  have hlim' := hlim.congr (Filter.Eventually.of_forall (fun N a ha =>
    Finset.sum_congr rfl (fun k _ => he a ha k)))
  exact hlim'.congr_right htarget

end NLS.Articles.KdVConvexity
