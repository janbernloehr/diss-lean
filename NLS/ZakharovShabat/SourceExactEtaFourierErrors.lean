import NLS.ZakharovShabat.SourceGapWeightedEta
import NLS.ZakharovShabat.SourceAngularBetaSeries

/-! Literal midpoint and terminal sine Fourier errors in the original
coefficient convention. Their definitions use the actual spectral data. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1≤p)]

def sourceExactEtaMidpointFourierError (hp : p≠⊤) (hp1 : 1<p) (ψ : CoeffPair p) (n : ℤ) : ℂ :=
  sourceDirichletMidpointDisplacement hp hp1 ψ n-(ψ.fst (-n)+ψ.snd n)/2

def sourceExactEtaSineFourierError (hp : p≠⊤) (hp1 : 1<p) (ψ : CoeffPair p) (n : ℤ) : ℂ :=
  sourceDirichletEtaSineNumerator hp hp1 n ψ-(I/2)*(ψ.fst (-n)-ψ.snd n)

end NLS.ZakharovShabat
