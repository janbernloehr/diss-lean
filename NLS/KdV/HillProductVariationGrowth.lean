import NLS.KdV.HillFrequencyDataVariation
import NLS.ComplexAnalysis.LinearFactorCircleDecay
import NLS.ZakharovShabat.Section7PsiPeriodUniqueness
import NLS.ZakharovShabat.SourcePsiVariationCombinationInterpolation

/-! Sub-sine growth of literal Hill products and their actual full
l2 variations follows from the proved frequency-product growth. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

theorem hillEnergySequenceProduct_pullback_sub_sine (n : ℕ+) (c : ℂ) (d : lp (fun _ : ℕ+ => ℂ) 2) :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∀ z ∈ sphere (0:ℂ) (centralCircleRadius k),
        ‖(2*z*hillEnergySequenceProduct n (z^2-c,d))/(-2*sin z)‖ ≤ ε := by
  exact linearFactor_circle_decay _ _ (fun z => -2*sin z) (((Real.pi:ℂ)*(n:ℕ))^2)
    (hillIndependentFrequency (c,d) ((n:ℕ):ℤ)) centralCircleRadius tendsto_centralCircleRadius_atTop
    (fun z => hillEnergyProduct_independent_candidate_filled n c d z)
    (section7_psi_sub_sine_growth (by norm_num) (by norm_num) ((n:ℕ):ℤ) (hillIndependentFrequencyDisplacement (c,d)))

theorem hillEnergyProductDataVariation_pullback_sub_sine (n : ℕ+) (c : ℂ)
    (d h : lp (fun _ : ℕ+ => ℂ) 2) (hd : (c,d) ∈ LpSequence.quadraticFrequencyDomain Real.pi)
    (hβ : hillIndependentFrequency (c,d) ((n:ℕ):ℤ) ≠ 0) (hn : h n = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∀ z ∈ sphere (0:ℂ) (centralCircleRadius k),
        ‖(2*z*hillEnergyProductDataVariation n d h (z^2-c))/(-2*sin z)‖ ≤ ε := by
  apply linearFactor_circle_decay _ _ (fun z => -2*sin z) (((Real.pi:ℂ)*(n:ℕ))^2)
    (hillIndependentFrequency (c,d) ((n:ℕ):ℤ)) centralCircleRadius tendsto_centralCircleRadius_atTop
    (fun z => hillEnergyProductDataVariation_frequency_filled n c d h hd hβ hn z)
  intro ε hε
  have hfree : Memℓp (fun k : ℤ => (Real.pi:ℂ)*k-(Real.pi:ℂ)*k) (2:ℝ≥0∞) := by
    simpa only [sub_self] using (zero_mem_ℓp' (E := fun _ : ℤ => ℂ) (p := (2:ℝ≥0∞)))
  obtain ⟨K,hK⟩ := eventually_atTop.mp (eventually_centralCircle_sourcePsiCandidateVariation_quotient_small
    (by norm_num) (by norm_num) (fun k : ℤ => (Real.pi:ℂ)*k) hfree ((n:ℕ):ℤ)
    (hillIndependentFrequencyDisplacement (c,d)) (hillIndependentFrequencyDataVariation c d h)
    (hillFrequencyDataVariation_omitted_zero c d h hd n hβ hn) hε)
  refine ⟨K,?_⟩
  intro k hk z hz
  have hb := (hK k hk z hz).2
  rw [entireSingleSpectralProduct_free] at hb
  exact hb

end NLS.KdV
