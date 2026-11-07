import NLS.ZakharovShabat.SourceExactEtaFourierErrors

/-! Exact original Fourier leading term of the literal eta terminal. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1≤p)]

theorem sourceExactEtaTerminal_fourier_decomposition
    (hp : p≠⊤) (hp1 : 1<p) (ψ : CoeffPair p) (n : ℤ) :
    -2*(sourceDirichletMidpointDisplacement hp hp1 ψ n+I*sourceDirichletEtaSineNumerator hp hp1 n ψ)+2*ψ.snd n=
      -2*(sourceExactEtaMidpointFourierError hp hp1 ψ n+I*sourceExactEtaSineFourierError hp hp1 ψ n) := by
  unfold sourceExactEtaMidpointFourierError sourceExactEtaSineFourierError
  ring_nf
  simp only [I_sq]
  ring

end NLS.ZakharovShabat
