import NLS.Poisson.SobolevBivector
import NLS.SequenceSpaces.SobolevPairGradient

/-! # Automatic Poisson regularity on conjugate Sobolev source domains

Both source exponents are finite. The full differentials have unique
gradients in reciprocal spaces, giving a bounded bilinear Poisson pairing.
The two base points may initially be independent; shared physical states
are handled by the intersection-domain interface.
-/
noncomputable section
open scoped ENNReal
namespace NLS.Poisson
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

def conjugateBivector (s : ℝ) (hp : p ≠ ⊤) (hq : q ≠ ⊤) :
    (WeightedCoeffPair (Weight.sobolev (-s)) q →L[ℂ] ℂ) →L[ℂ]
      (WeightedCoeffPair (Weight.sobolev s) p →L[ℂ] ℂ) →L[ℂ] ℂ :=
  (signedBivector s).bilinearComp
    ((negNegComponents (p := p) s).comp
      (WeightedCoeffPair.sobolevCotangentComponentsCLM (p := q) (q := p) (-s) hq))
    (WeightedCoeffPair.sobolevCotangentComponentsCLM (p := p) (q := q) s hp)

theorem norm_conjugateBivector_le (s : ℝ) (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (L : WeightedCoeffPair (Weight.sobolev (-s)) q →L[ℂ] ℂ)
    (M : WeightedCoeffPair (Weight.sobolev s) p →L[ℂ] ℂ) :
    ‖conjugateBivector s hp hq L M‖ ≤ 2*‖L‖*‖M‖ := by
  apply (norm_signedBivector_le s _ _).trans
  change 2*‖negNegComponents s
    (WeightedCoeffPair.sobolevCotangentComponentsCLM (p := q) (q := p) (-s) hq L)‖*
    ‖WeightedCoeffPair.sobolevCotangentComponentsCLM (p := p) (q := q) s hp M‖ ≤ 2*‖L‖*‖M‖
  rw [norm_negNegComponents]
  gcongr <;> apply WeightedCoeffPair.norm_sobolevCotangentComponentsCLM_le

theorem analyticOnNhd_conjugateBracket (s : ℝ) (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (F : WeightedCoeffPair (Weight.sobolev (-s)) q → ℂ)
    (G : WeightedCoeffPair (Weight.sobolev s) p → ℂ)
    {UF : Set (WeightedCoeffPair (Weight.sobolev (-s)) q)}
    {UG : Set (WeightedCoeffPair (Weight.sobolev s) p)}
    (hF : AnalyticOnNhd ℂ F UF) (hG : AnalyticOnNhd ℂ G UG) :
    AnalyticOnNhd ℂ (fun xy : WeightedCoeffPair (Weight.sobolev (-s)) q × WeightedCoeffPair (Weight.sobolev s) p =>
      conjugateBivector s hp hq (fderiv ℂ F xy.1) (fderiv ℂ G xy.2)) (UF ×ˢ UG) := by
  intro x hx
  exact ((conjugateBivector s hp hq).analyticAt_bilinear _).comp₂
    ((hF.fderiv x.1 hx.1).comp ((ContinuousLinearMap.fst ℂ _ _).analyticAt x))
    ((hG.fderiv x.2 hx.2).comp ((ContinuousLinearMap.snd ℂ _ _).analyticAt x))


end NLS.Poisson
