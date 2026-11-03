import NLS.KdV.HillGapNumeratorDecay
import NLS.KdV.HillIntrinsicPeriodLinearity
import NLS.ComplexAnalysis.SimpleZeroInterpolation

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem entire_eq_zero_of_hill_periods_and_product_decay
    (N : ℂ → ℂ) (hN : AnalyticOnNhd ℂ N univ)
    (hreal : ∀ x : ℝ, (N (x : ℂ)).im = 0)
    (hperiods : ∀ k : ℕ, 1 ≤ k → hillIntrinsicGapPeriod q hq hr k N = 0)
    (hdecay : ∀ roots ∈ hillGapRootBox q hq hr, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ k : ℕ in atTop, ∀ E ∈ sphere (0 : ℂ) ((centralCircleRadius k)^2),
        ‖N E/hillAbelianNumeratorProduct roots 0 E‖ ≤ ε) : N = 0 := by
  have hex (j : ℕ) : ∃ E ∈ segment ℝ (hillRealLabels q hq hr (2*(j+1)-1) : ℂ)
      (hillRealLabels q hq hr (2*(j+1)) : ℂ), N E = 0 :=
    exists_zero_on_hillRealGap_of_intrinsic_period_zero q hq hr N hN (j+1) (by omega)
      (fun x _ => hreal x) (hperiods (j+1) (by omega))
  choose energy hseg hzero using hex
  let roots : ℕ → ℝ := fun j => (energy j).re
  have he (j : ℕ) : (roots j : ℂ) = energy j := by
    apply Complex.ext
    · rfl
    · simpa only [ofReal_im] using (im_eq_zero_of_mem_real_segment _ _ _ (hseg j)).symm
  have hroots : roots ∈ hillGapRootBox q hq hr := by
    intro j
    exact re_mem_Icc_of_mem_real_segment _ _ (monotone_hillRealLabels q hq hr (by omega)) _ (hseg j)
  obtain ⟨K,hK⟩ := exists_hillGapFullEnergyProduct_ratio_bound q hq hr roots roots hroots hroots
  have hcommon (E : ℂ) (hz : hillAbelianNumeratorProduct roots 0 E = 0) : N E = 0 := by
    obtain ⟨j,_,hj⟩ := (hillAbelianNumeratorProduct_zero_iff q hq hr roots hroots 0 E).mp hz
    rw [← hj,he j]
    exact hzero j
  refine entire_eq_zero_of_simple_zero_interpolation hN
    (analyticOnNhd_hillAbelianNumeratorProduct q hq hr roots hroots 0)
    hcommon (fun E hz => hillGapFullEnergyProduct_simple_zeros q hq hr roots hroots E hz)
    (fun k => (centralCircleRadius (k+K))^2)
    (tendsto_hillEnergyCircleRadius.comp (tendsto_add_atTop_nat K))
    (fun k E hE => (hK (k+K) (by omega) E hE).1) ?_
  intro ε hε
  exact (tendsto_add_atTop_nat K).eventually (hdecay roots hroots ε hε)

end NLS.KdV
