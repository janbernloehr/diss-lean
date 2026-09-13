import NLS.ZakharovShabat.WeightedDomainPotential
import NLS.ZakharovShabat.ComplementaryAnalytic

/-!
# Joint analytic dependence of the complementary potential operator

Weighted convolution makes the derivative-domain potential continuous linear
in the potential. Composition with the complementary analytic extension then
gives joint operator-norm analyticity in the potential and spectral parameter.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The weighted domain potential has an exponent-only bilinear norm bound. -/
theorem norm_weightedDomainPotential_le (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (f : WeightedDomain w.toWeight p) :
    ‖weightedDomainPotential hp w φ f‖ ≤ (WeightedCoeff.sobolevEmbeddingConstant p hp * ‖φ‖) * ‖f‖ := by
  have hb (a : WeightedCoeff w.toWeight p) (ha : ‖a‖ ≤ ‖φ‖) (g : WeightedCoeff w.toWeight.oneDerivative p) :
      ‖w.convolutionCLM a (weightedDomainScalarL1 hp w.toWeight g)‖ ≤
        (WeightedCoeff.sobolevEmbeddingConstant p hp * ‖φ‖) * ‖g‖ := by
    calc
      _ ≤ ‖a‖ * ‖weightedDomainScalarL1 hp w.toWeight g‖ := w.norm_convolution_le _ _
      _ ≤ ‖φ‖ * (WeightedCoeff.sobolevEmbeddingConstant p hp * ‖g‖) :=
        mul_le_mul ha (norm_weightedDomainScalarL1_le hp w.toWeight g) (norm_nonneg _) (norm_nonneg _)
      _ = _ := by ring
  have h := WeightedCoeffPair.norm_mapComponents_le hp w.toWeight.oneDerivative w.toWeight
    ((w.convolutionCLM φ.fst).comp (weightedDomainScalarL1 hp w.toWeight))
    ((w.convolutionCLM φ.snd).comp (weightedDomainScalarL1 hp w.toWeight))
    (mul_nonneg (WeightedCoeff.sobolevEmbeddingConstant_nonneg p hp) (norm_nonneg φ))
    (hb φ.fst (WithLp.norm_fst_le _ φ)) (hb φ.snd (WithLp.norm_snd_le _ φ))
    ((LinearIsometryEquiv.withLpProdComm p ℂ (WeightedCoeff w.toWeight.oneDerivative p)
      (WeightedCoeff w.toWeight.oneDerivative p)) f)
  change ‖weightedDomainPotential hp w φ f‖ ≤ _ at h
  simpa only [LinearIsometryEquiv.norm_map] using h

/-- Continuous complex-linear dependence of the actual domain potential. -/
def weightedDomainPotentialCLM (hp : p ≠ ⊤) (w : SpectralWeight) :
    WeightedCoeffPair w.toWeight p →L[ℂ]
      (WeightedDomain w.toWeight p →L[ℂ] WeightedCoeffPair w.toWeight p) :=
  LinearMap.mkContinuous
    { toFun := weightedDomainPotential hp w
      map_add' := by
        intro φ ψ
        apply ContinuousLinearMap.ext
        intro f
        apply (WeightedCoeffPair.toMax w.toWeight p).injective
        apply Prod.ext
        · change w.convolution (φ.fst + ψ.fst) _ = w.convolution φ.fst _ + w.convolution ψ.fst _
          exact w.convolution_add_left _ _ _
        · change w.convolution (φ.snd + ψ.snd) _ = w.convolution φ.snd _ + w.convolution ψ.snd _
          exact w.convolution_add_left _ _ _
      map_smul' := by
        intro c φ
        apply ContinuousLinearMap.ext
        intro f
        apply (WeightedCoeffPair.toMax w.toWeight p).injective
        apply Prod.ext
        · change w.convolution (c • φ.fst) _ = c • w.convolution φ.fst _
          exact w.convolution_smul_left _ _ _
        · change w.convolution (c • φ.snd) _ = c • w.convolution φ.snd _
          exact w.convolution_smul_left _ _ _ }
    (WeightedCoeff.sobolevEmbeddingConstant p hp)
    (fun φ => ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (WeightedCoeff.sobolevEmbeddingConstant_nonneg p hp) (norm_nonneg φ))
      (norm_weightedDomainPotential_le hp w φ))

@[simp] theorem weightedDomainPotentialCLM_apply (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) : weightedDomainPotentialCLM hp w φ = weightedDomainPotential hp w φ := rfl

/-- Total extension of the actual operator `T_n=Φ A_λ⁻¹Q_n`. -/
def weightedPotentialExtension (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) :
    WeightedCoeffPair w.toWeight p →L[ℂ] WeightedCoeffPair w.toWeight p :=
  (weightedDomainPotential hp w φ).comp (complementaryDomainExtension w.toWeight n z)

/-- The total extension agrees with `T_n` on the full closed strip. -/
theorem weightedPotentialExtension_eq (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    weightedPotentialExtension hp w φ n z = weightedPotentialInverse hp w φ n z hz := by
  rw [weightedPotentialExtension, complementaryDomainExtension_eq w.toWeight n z hz]
  exact ContinuousLinearMap.ext (fun f => weightedDomainPotential_complementaryInverse hp w φ f n z hz)

/-- Joint analyticity in the potential and spectral parameter, in operator norm. -/
theorem analyticAt_weightedPotentialExtension (hp : p ≠ ⊤) (w : SpectralWeight) (n : ℤ)
    (s : WeightedCoeffPair w.toWeight p × ℂ)
    (hs : IsUnit (complementaryNormalizedPencil (p := p) w.toWeight n s.2)) :
    AnalyticAt ℂ (fun t : WeightedCoeffPair w.toWeight p × ℂ => weightedPotentialExtension hp w t.1 n t.2) s := by
  exact ((ContinuousLinearMap.compL ℂ (WeightedCoeffPair w.toWeight p) (WeightedDomain w.toWeight p)
    (WeightedCoeffPair w.toWeight p)).analyticAt_bilinear _).comp₂
    (((weightedDomainPotentialCLM hp w).analyticAt s.1).comp analyticAt_fst)
    ((analyticAt_complementaryDomainExtension w.toWeight n s.2 hs).comp analyticAt_snd)

end NLS.ZakharovShabat
