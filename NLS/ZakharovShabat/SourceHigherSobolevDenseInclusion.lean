import NLS.ZakharovShabat.SourceHigherSobolevRealGerm
import NLS.SequenceSpaces.FiniteSourceDensity
import NLS.SequenceSpaces.WeightedFiniteCoefficients
import NLS.ComplexAnalysis.DenseLinearConnectedPreimage
/-! # Density of the original higher Sobolev source inclusion -/
noncomputable section
open Set
namespace NLS.ZakharovShabat

/-- Every integer Sobolev source space has dense image in the original Hilbert source. -/
theorem higherSobolevSourceInclusion_denseRange (s : ℕ) : DenseRange (higherSobolevSourceInclusion s) := by
  intro ψ
  apply closure_mono (s := range (CoeffPair.ofFinsupp (p := 2))) ?_ (CoeffPair.denseRange_ofFinsupp (by simp) ψ)
  rintro _ ⟨a,rfl⟩
  refine ⟨(WeightedCoeff.ofFinsupp (Weight.sobolev (s : ℝ)) 2 a.1,
    WeightedCoeff.ofFinsupp (Weight.sobolev (s : ℝ)) 2 a.2),?_⟩
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext
  · ext n
    change (higherSobolevSourceInclusion s _).fst n = _
    rw [higherSobolevSourceInclusion_fst]
    rfl
  · ext n
    change (higherSobolevSourceInclusion s _).snd n = _
    rw [higherSobolevSourceInclusion_snd]
    rfl
end NLS.ZakharovShabat
