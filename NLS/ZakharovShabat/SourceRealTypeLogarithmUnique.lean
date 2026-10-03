import NLS.ZakharovShabat.SourceRealTypeProjection
import NLS.ComplexAnalysis.ContinuousLogarithmUnique

/-! # Logarithm uniqueness on overlaps of real-centered source balls

The real projection stays in both balls. Agreement on the real source
form therefore fixes continuous logarithms throughout a complex-source
overlap whenever their exponentials agree.
-/
noncomputable section
open Set Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceRealTypeProjection_mem_ball (hp : p ≠ ⊤) (φ : realTypeSourceSubmodule p)
    (r : ℝ) (ψ : CoeffPair p) (hψ : ψ ∈ Metric.ball φ.val r) :
    (sourceRealTypeProjection hp ψ).val ∈ Metric.ball φ.val r := by
  have hd := (lipschitzWith_sourceRealPart hp).dist_le_mul ψ φ.val
  have hfix : sourceRealPart φ.val = φ.val := sourceRealTypeProjection_val_of_realType hp φ.val φ.property
  simp only [NNReal.coe_one,one_mul,hfix] at hd
  exact hd.trans_lt hψ

/-- Equal real-source normalizations fix the logarithm on an entire
complex-source overlap, with no principal-branch assumption. -/
theorem continuous_sourceLogarithms_eqOn (hp : p ≠ ⊤)
    (φ χ : realTypeSourceSubmodule p) (r s : ℝ) (F G : CoeffPair p → ℂ)
    (hF : ContinuousOn F (Metric.ball φ.val r ∩ Metric.ball χ.val s))
    (hG : ContinuousOn G (Metric.ball φ.val r ∩ Metric.ball χ.val s))
    (hexp : ∀ ψ ∈ Metric.ball φ.val r ∩ Metric.ball χ.val s, exp (F ψ) = exp (G ψ))
    (hreal : ∀ ψ : realTypeSourceSubmodule p, ψ.val ∈ Metric.ball φ.val r ∩ Metric.ball χ.val s → F ψ.val = G ψ.val) :
    EqOn F G (Metric.ball φ.val r ∩ Metric.ball χ.val s) := by
  intro ψ hψ
  let a := sourceRealTypeProjection hp ψ
  have ha : a.val ∈ Metric.ball φ.val r ∩ Metric.ball χ.val s :=
    ⟨sourceRealTypeProjection_mem_ball hp φ r ψ hψ.1,sourceRealTypeProjection_mem_ball hp χ s ψ hψ.2⟩
  exact continuousLogarithms_eqOn F G _ ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected
    hF hG hexp a.val ha (hreal a ha) hψ

end NLS.ZakharovShabat
