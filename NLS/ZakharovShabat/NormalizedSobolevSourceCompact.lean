import NLS.ZakharovShabat.NormalizedWeightedSourceTopology
import NLS.ZakharovShabat.SourceSection14WeightedMembership
import NLS.SequenceSpaces.CompactSobolevInclusion

/-! # Compact decoding at every positive Sobolev order

The exact half-scale normalization gives the symbol ⟨n⟩⁻ᵗ. Its membership
in some finite sequence exponent proves compactness for every t > 0.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Positive fractional regularity already makes the actual decoder compact. -/
theorem isCompactOperator_normalizedSobolevSource (t : ℝ) (ht : 0 < t) :
    IsCompactOperator
      (normalizedWeightedSourceCLM (p := p) (sourceSobolevSpectralWeight t ht.le)) := by
  let w := sourceSobolevSpectralWeight t ht.le
  obtain ⟨q,instQ,hq,hm⟩ := Weight.exists_finite_exponent_negative_sobolev t ht
  let : Fact (1 ≤ q) := instQ
  let a : Coeff q := ⟨fun n => (Weight.sobolev (-t) n : ℂ),hm⟩
  let m := Coeff.exponentInclusion (show q ≤ ⊤ from le_top) a
  have heSymbol (n : ℤ) : m n = (w (2*n) : ℂ)⁻¹ := by
    change (Weight.sobolev (-t) n : ℂ) = (w (2*n) : ℂ)⁻¹
    simp only [w,sourceSobolevSpectralWeight_even,Weight.sobolev,Real.rpow_neg
      (by positivity : (0:ℝ) ≤ 1 + |(n:ℝ)|),Complex.ofReal_inv]
  let M := Coeff.multiplierCLM (p := p) m
  have hM : IsCompactOperator M := Coeff.isCompactOperator_multiplier_of_finite_symbol hq a
  have h₁ := (hM.comp_clm (ContinuousLinearMap.fst ℂ (Coeff p) (Coeff p))).clm_comp
    (ContinuousLinearMap.inl ℂ (Coeff p) (Coeff p))
  have h₂ := (hM.comp_clm (ContinuousLinearMap.snd ℂ (Coeff p) (Coeff p))).clm_comp
    (ContinuousLinearMap.inr ℂ (Coeff p) (Coeff p))
  have hprod : IsCompactOperator (M.prodMap M) := by
    have he : (M.prodMap M : (Coeff p × Coeff p) → (Coeff p × Coeff p)) =
        (fun a => (M a.1,0))+(fun a => (0,M a.2)) := by
      funext a
      change (M a.1,M a.2) = (M a.1+0,0+M a.2)
      simp
    rw [he]
    exact h₁.add h₂
  have he : normalizedWeightedSourceCLM (p := p) w =
      (CoeffPair.toMax p).symm.toContinuousLinearMap.comp
        ((M.prodMap M).comp (CoeffPair.toMax p).toContinuousLinearMap) := by
    apply ContinuousLinearMap.ext
    intro b
    apply (CoeffPair.toMax p).injective
    apply Prod.ext <;> ext n <;>
      simp [M,heSymbol,div_eq_mul_inv,mul_comm]
  rw [he]
  exact (hprod.comp_clm (CoeffPair.toMax p).toContinuousLinearMap).clm_comp
    (CoeffPair.toMax p).symm.toContinuousLinearMap

end NLS.ZakharovShabat
