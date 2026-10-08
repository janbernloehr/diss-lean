import NLS.ComplexAnalysis.SourceLemmaE2
import NLS.ZakharovShabat.SourceRealTypeDecomposition

/-! # E.2 on the actual Fourier source real form

The physical real and imaginary projections already have the continuity
bounds needed for local uniqueness. Connectedness propagates the identity
through the whole complex domain, without assuming convexity or requiring
that the domain contain every real-type source.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The real-form identity theorem for the actual source coefficient space. -/
theorem sourceLemmaE2_realType (hp : p ≠ ⊤) (U : Set (CoeffPair p))
    (hU : IsOpen U) (hconn : IsConnected U) (hreal : (U ∩ realTypeSourceLocus p).Nonempty)
    (f : CoeffPair p → F) (hf : AnalyticOnNhd ℂ f U)
    (hzero : EqOn f 0 (U ∩ realTypeSourceLocus p)) : EqOn f 0 U := by
  obtain ⟨φ,hφU,hφR⟩ := hreal
  have hgerm := NLS.ComplexAnalysis.DifferentiableOn.eventually_eq_zero_of_real_form
    (realTypeSourceLocus p) φ hφR (by
      intro x y hx hy
      change IsRealType (CoeffPair.toMax p (x+y))
      rw [map_add]
      exact hx.add hy) (by
      intro t x hx
      change IsRealType (CoeffPair.toMax p ((t:ℂ) • x))
      rw [map_smul]
      exact hx.ofReal_smul t)
    sourceRealPart sourceImagPart sourceRealPart_realType sourceImagPart_realType
    (fun v => (sourceRealPart_add_I_smul_sourceImagPart v).symm)
    (norm_sourceRealPart_le hp) (norm_sourceImagPart_le hp)
    U hU hφU f hf.differentiableOn (fun _ hx hr => hzero ⟨hx,hr⟩)
  exact hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn.isPreconnected hφU hgerm

end NLS.ZakharovShabat
