import NLS.ZakharovShabat.SourceRealActionBallOverlap
import NLS.ComplexAnalysis.RealFormIdentity
import NLS.ComplexAnalysis.ConvexHolomorphicIdentity

/-!
# Banach-valued identity on real-centered source balls

Projection onto the real-type source locus places a real source in every
nonempty overlap. Equality on the real locus gives equality of a complex
germ, and convex continuation identifies the maps on the entire overlap.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem eqOn_sourceRealCenteredBalls_of_real_agreement
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (hp : p ≠ ⊤) (φ₀ φ₁ : realTypeSourceLocus p) (r₀ r₁ : ℝ)
    (f g : CoeffPair p → F)
    (hf : DifferentiableOn ℂ f (ball φ₀.val r₀))
    (hg : DifferentiableOn ℂ g (ball φ₁.val r₁))
    (hreal : ∀ χ : realTypeSourceLocus p,
      χ.val ∈ ball φ₀.val r₀ ∩ ball φ₁.val r₁ → f χ.val = g χ.val) :
    EqOn f g (ball φ₀.val r₀ ∩ ball φ₁.val r₁) := by
  intro ψ hψ
  obtain ⟨θ,hθreal,hθ⟩ := exists_realType_mem_inter_sourceBalls hp
    φ₀.val φ₁.val φ₀.property φ₁.property r₀ r₁ ψ hψ
  let V := ball φ₀.val r₀ ∩ ball φ₁.val r₁
  let H : CoeffPair p → F := fun χ => f χ-g χ
  have hdiff : DifferentiableOn ℂ H V :=
    (hf.mono inter_subset_left).sub (hg.mono inter_subset_right)
  have hzero : ∀ χ ∈ V, χ ∈ realTypeSourceLocus p → H χ = 0 := by
    intro χ hχ hχreal
    exact sub_eq_zero.mpr (hreal ⟨χ,hχreal⟩ hχ)
  have hlocal := NLS.ComplexAnalysis.DifferentiableOn.eventually_eq_zero_of_real_form
    (realTypeSourceLocus p) θ hθreal
    (by
      intro x y hx hy
      change IsRealType (CoeffPair.toMax p (x+y))
      rw [map_add]
      exact hx.add hy)
    (by
      intro t x hx
      change IsRealType (CoeffPair.toMax p ((t:ℂ) • x))
      rw [map_smul]
      exact hx.ofReal_smul t)
    sourceRealPart sourceImagPart sourceRealPart_realType sourceImagPart_realType
    (fun χ => (sourceRealPart_add_I_smul_sourceImagPart χ).symm)
    (norm_sourceRealPart_le hp) (norm_sourceImagPart_le hp)
    V (isOpen_ball.inter isOpen_ball) hθ H hdiff hzero
  have heq : f =ᶠ[𝓝 θ] g := hlocal.mono (fun _ h => sub_eq_zero.mp h)
  exact NLS.ComplexAnalysis.DifferentiableOn.eqOn_of_convex_of_eventuallyEq
    f g V (isOpen_ball.inter isOpen_ball) ((convex_ball _ _).inter (convex_ball _ _))
    (hf.mono inter_subset_left) (hg.mono inter_subset_right) θ hθ heq (x := ψ) hψ

end NLS.ZakharovShabat
