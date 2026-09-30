import NLS.Poisson.SourceBracket
import NLS.ZakharovShabat.SourceRealTypeFiniteApproximation

/-! # Extending source bracket identities from finite real potentials

Analytic source brackets are continuous. Symmetric Fourier approximation
therefore transports an identity proved at finite real potentials to
every real source in an open domain, including domains with removed gap
loci. The finite identity is an explicit hypothesis, not an imported
canonical-bracket axiom.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.Poisson
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceBracket_eq_of_finite_realType (hp : p ≠ ⊤) (h2p : (2:ℝ≥0∞) ≤ p)
    {U : Set (CoeffPair p)} (hU : IsOpen U) {F G : CoeffPair p → ℂ}
    (hF : AnalyticOnNhd ℂ F U) (hG : AnalyticOnNhd ℂ G U) (c : ℂ)
    (hfinite : ∀ ψ ∈ U, ZakharovShabat.IsRealType (CoeffPair.toMax p ψ) →
      Coeff.HasFiniteSupport ψ.fst → Coeff.HasFiniteSupport ψ.snd → sourceBracket h2p F G ψ = c)
    (φ : CoeffPair p) (hφ : φ ∈ U) (hreal : ZakharovShabat.IsRealType (CoeffPair.toMax p φ)) :
    sourceBracket h2p F G φ = c :=
  ZakharovShabat.eq_of_continuousOn_of_finite_realType hp hU
    (analyticOnNhd_sourceBracket h2p hF hG).continuousOn c hfinite φ hφ hreal

end NLS.Poisson
