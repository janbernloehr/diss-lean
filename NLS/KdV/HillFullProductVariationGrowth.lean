import NLS.KdV.HillFullFrequencyDataVariation
import NLS.ZakharovShabat.SourcePsiFullProductInterpolation
import NLS.ZakharovShabat.Section7PsiPeriodUniqueness

/-! The full energy numerator variation has sub-sine pullback growth
for EVERY complex l2 direction, by the proved full frequency variation
estimate. No omitted-index constraint or new growth axiom is needed. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

theorem hillEnergyFullProductDataVariation_pullback_sub_sine (c : ℂ)
    (d h : lp (fun _ : ℕ+ => ℂ) 2) (hd : (c,d) ∈ LpSequence.quadraticFrequencyDomain Real.pi) :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∀ z ∈ sphere (0:ℂ) (centralCircleRadius k),
        ‖(2*z*hillEnergyFullProductDataVariation d h (z^2-c))/(-2*sin z)‖ ≤ ε := by
  intro ε hε
  have hfree : Memℓp (fun k : ℤ => (Real.pi:ℂ)*k-(Real.pi:ℂ)*k) (2:ℝ≥0∞) := by
    simpa only [sub_self] using (zero_mem_ℓp' (E := fun _ : ℤ => ℂ) (p := (2:ℝ≥0∞)))
  obtain ⟨K,hK⟩ := eventually_centralCircle_sourcePsiFullProductVariation_quotient_small
    (by norm_num) (by norm_num) (fun k : ℤ => (Real.pi:ℂ)*k) hfree
    (hillIndependentFrequencyDisplacement (c,d)) (hillIndependentFrequencyDataVariation c d h) hε
  refine ⟨K,?_⟩
  intro k hk z hz
  have hb := (hK k hk z hz).2
  rw [entireSingleSpectralProduct_free,hillEnergyFullProductDataVariation_frequency c d h hd z] at hb
  have he : -2*z*hillEnergyFullProductDataVariation d h (z^2-c) = -(2*z*hillEnergyFullProductDataVariation d h (z^2-c)) := by ring
  simpa only [he,neg_div,norm_neg] using hb

end NLS.KdV
