import NLS.Articles.KdVPseudomeasures.SpectralInverseRestriction
import NLS.ComplexAnalysis.NearIdentityImageInverse

/-! Source Proposition2.18 with an actual analytic inverse on an OPEN
neighborhood of the ENTIRE image of the closed original source ball. -/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue NLS.KdV
open NLS.ComplexAnalysis

/-- The actual adapted map is analytically invertible near its entire closed
source-ball image,with the source constants,closed half-ball coverage and exact
physical source constraints. One cutoff precedes BOTH weights and potentials. -/
theorem sourceProposition2_18 (r : ℝ) (hr : AdmissiblePredualOrder r) (m : ℝ) (hm : 1 ≤ m) :
    ∃ N : ℕ, 1 ≤ N ∧
      (∀ n : ℕ, 1 ≤ n → N ≤ n → endpointHillConstant r*(n:ℝ)^(r-1/2)*(64*(2*m)) ≤ 1/2) ∧
      ∀ w : SpectralWeight,
      ∃ V : Set (PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤),
      ∃ g : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤ →
          PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤,
        IsOpen V ∧
        sourceWeightedAdaptedFourier w r hr N '' closedBall 0 m ⊆ V ∧
        closedBall 0 (m/2) ⊆ sourceWeightedAdaptedFourier w r hr N '' closedBall 0 m ∧
        AnalyticOnNhd ℂ (sourceWeightedAdaptedFourier w r hr N) (ball 0 (2*m)) ∧
        AnalyticOnNhd ℂ g V ∧
        Set.InjOn (sourceWeightedAdaptedFourier w r hr N) (closedBall 0 m) ∧
        (∀ q, ‖q‖ ≤ m → g (sourceWeightedAdaptedFourier w r hr N q) = q ∧
          ‖fderiv ℂ (sourceWeightedAdaptedFourier w r hr N) q-ContinuousLinearMap.id ℂ _‖ ≤ (1/16 : ℝ) ∧
          (1/2 : ℝ)*‖q‖ ≤ ‖sourceWeightedAdaptedFourier w r hr N q‖ ∧
            ‖sourceWeightedAdaptedFourier w r hr N q‖ ≤ 2*‖q‖) ∧
        ∀ y ∈ V, g y ∈ ball 0 (3*m/2) ∧ sourceWeightedAdaptedFourier w r hr N (g y) = y ∧
          ((g y).val.IsRealMeanZeroPeriodOne ↔ y.val.IsRealMeanZeroPeriodOne) := by
  have hmpos : 0 < m := by linarith
  obtain ⟨N, hN, hcut, hmap⟩ := source_uniform_adaptedFourier_inverse r hr m hmpos
  refine ⟨N, hN, hcut, fun w => ?_⟩
  let : CompleteSpace (PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤) :=
    PeriodicFourierLebesgue.completeSpace _ _ (w.hasTemperedInverse_negativeSobolev r)
  obtain ⟨hf, hbounds, g₀, _, hinj, hright₀, _, _⟩ := hmap w
  have hb (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤) (hq : q ∈ ball 0 (2*m)) :
      ‖sourceWeightedAdaptedFourier w r hr N q-q‖ ≤ m/32 := by
    have hh := (sourceWeightedAdaptedFourier_spec w r hr N (2*m) (by positivity)
      hcut q (mem_ball_zero_iff.mp hq).le).2
    linarith
  obtain ⟨g, hopen, hA, hi, hleft, hright⟩ :=
    exists_analytic_inverse_on_near_identity_image (sourceWeightedAdaptedFourier w r hr N) m hmpos hf hb
  let V := sourceWeightedAdaptedFourier w r hr N '' ball 0 (3*m/2)
  refine ⟨V, g, hopen, ?_, ?_, hf, hA, hinj, ?_, ?_⟩
  · rintro y ⟨q, hq, rfl⟩
    have hqn : ‖q‖ ≤ m := by simpa only [mem_closedBall, dist_zero_right] using hq
    have hqm : q ∈ ball 0 (3*m/2) := by rw [mem_ball_zero_iff]; linarith
    exact ⟨q, hqm, rfl⟩
  · intro y hy
    have hyn : ‖y‖ ≤ m/2 := by simpa only [mem_closedBall, dist_zero_right] using hy
    obtain ⟨hgm, hfy⟩ := hright₀ y (by linarith)
    exact ⟨g₀ y, ball_subset_closedBall hgm, hfy⟩
  · intro q hq
    exact ⟨hleft q (by rw [mem_ball_zero_iff]; linarith), hbounds q hq⟩
  · intro y hy
    obtain ⟨hgy, hfy⟩ := hright y hy
    have hgn : ‖g y‖ ≤ 2*m := by have hh := mem_ball_zero_iff.mp hgy; linarith
    have hp := sourceWeightedAdaptedFourier_preserves_complex_source w r hr N (2*m)
      (by positivity) hcut (g y) hgn
    rw [hfy] at hp
    have hreal : (g y).val = (g y).val.conjugate ↔ y.val = y.val.conjugate := by
      constructor
      · intro hgr
        have hh := sourceWeightedAdaptedFourier_real w r hr N (2*m) (by positivity) hcut (g y) hgn hgr
        simpa only [hfy] using hh
      · intro hyr
        have hc := sourceWeightedAdaptedFourier_conj w r hr N (2*m) (by positivity) hcut (g y) hgn
        rw [hfy] at hc
        have hfc : sourceWeightedAdaptedFourier w r hr N (sourceWeightedConjugate w r (g y)) = y :=
          Subtype.ext (hc.trans hyr.symm)
        have hCmem : sourceWeightedConjugate w r (g y) ∈ ball 0 (3*m/2) := by
          simpa only [mem_ball_zero_iff, norm_sourceWeightedConjugate] using mem_ball_zero_iff.mp hgy
        have he := hi hCmem hgy (hfc.trans hfy.symm)
        exact (congrArg Subtype.val he).symm
    refine ⟨hgy, hfy, ?_⟩
    simp only [Distribution.IsRealMeanZeroPeriodOne, hreal, ← hp.1, ← hp.2]

end NLS.Articles.KdVPseudomeasures
