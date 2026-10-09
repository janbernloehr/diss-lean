import NLS.ComplexAnalysis.HermitianPairFourierAssembly
import NLS.ZakharovShabat.ClassicalCharacteristicGradientSummability

/-! # Both components of the actual characteristic gradients

The coefficients are vector-valued Fourier integrals in the Hermitian norm.
The anti-discriminant's lattice reference uses the physical waves with indices 2*n and -2*n;
SourceCorollaryG6ReferenceAudit treats the extra pi in the printed subscripts.
-/
noncomputable section
open Set Complex MeasureTheory NLS.ComplexAnalysis NLS.Fourier NLS.LinearVolterra
open scoped ENNReal
namespace NLS.ZakharovShabat

def hermitianCharacteristicGradientAssembly {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (F : ((ℂ × ℂ) →L[ℝ] ℂ) → Coeff q) : HermitianPairCoeff q :=
  I • hermitianPairFourierAssembly (F (ContinuousLinearMap.fst ℝ ℂ ℂ))
    (F (ContinuousLinearMap.snd ℝ ℂ ℂ))

theorem norm_hermitianCharacteristicGradientAssembly_le {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (F : ((ℂ × ℂ) →L[ℝ] ℂ) → Coeff q) (K : ℝ)
    (hF : ∀ P, ‖P‖ ≤ 1 → ‖F P‖ ≤ K) : ‖hermitianCharacteristicGradientAssembly F‖ ≤ 2*K := by
  rw [hermitianCharacteristicGradientAssembly,norm_smul,norm_I,one_mul]
  exact (norm_hermitianPairFourierAssembly_le _ _).trans (by
    linarith [hF _ (ContinuousLinearMap.norm_fst_le ℝ ℂ ℂ),hF _ (ContinuousLinearMap.norm_snd_le ℝ ℂ ℂ)])

/-- Full Fourier sequence of i times the actual discriminant gradient. -/
def classicalHermitianDiscriminantGradientCoefficients {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 1 < q)
    (φ : Curve (ℂ × ℂ)) (z : ℂ) : HermitianPairCoeff q :=
  hermitianCharacteristicGradientAssembly (classicalDiscriminantGradientFourierCoefficients hq φ z)

/-- Full Fourier sequence of i times the anti-discriminant gradient error. -/
def classicalHermitianAntiDiscriminantGradientCoefficients {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 1 < q)
    (φ : Curve (ℂ × ℂ)) (z w : ℂ) : HermitianPairCoeff q :=
  hermitianCharacteristicGradientAssembly (classicalAntiDiscriminantGradientFourierCoefficients hq φ z w)

theorem classicalHermitianDiscriminantGradientCoefficients_apply {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 1 < q)
    (φ : Curve (ℂ × ℂ)) (z : ℂ) (k : ℤ) :
    classicalHermitianDiscriminantGradientCoefficients hq φ z k =
      ∫ t in (0 : ℝ)..1, wave (-k) (2*t) • (I • hermitianPair (classicalDiscriminantGradient φ z t)) := by
  change I • hermitianPairFourierAssembly
    (classicalDiscriminantGradientFourierCoefficients hq φ z (ContinuousLinearMap.fst ℝ ℂ ℂ))
    (classicalDiscriminantGradientFourierCoefficients hq φ z (ContinuousLinearMap.snd ℝ ℂ ℂ)) k = _
  rw [hermitianPairFourierAssembly_apply]
  simp only [classicalDiscriminantGradientFourierCoefficients_apply,
    ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd']
  rw [hermitianPair_intervalFourierCoefficient _ _
    (continuous_classicalDiscriminantGradient φ z).fst (continuous_classicalDiscriminantGradient φ z).snd]
  rw [← intervalIntegral.integral_smul]
  congr 1
  funext t
  exact smul_comm _ _ _

theorem classicalHermitianAntiDiscriminantGradientCoefficients_apply {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 1 < q)
    (φ : Curve (ℂ × ℂ)) (z w : ℂ) (k : ℤ) :
    classicalHermitianAntiDiscriminantGradientCoefficients hq φ z w k =
      ∫ t in (0 : ℝ)..1, wave (-k) (2*t) • (I • hermitianPair (classicalAntiDiscriminantGradientRemainder φ z w t)) := by
  change I • hermitianPairFourierAssembly
    (classicalAntiDiscriminantGradientFourierCoefficients hq φ z w (ContinuousLinearMap.fst ℝ ℂ ℂ))
    (classicalAntiDiscriminantGradientFourierCoefficients hq φ z w (ContinuousLinearMap.snd ℝ ℂ ℂ)) k = _
  rw [hermitianPairFourierAssembly_apply]
  simp only [classicalAntiDiscriminantGradientFourierCoefficients_apply,
    ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd']
  have hc : Continuous (classicalAntiDiscriminantGradientRemainder φ z w) := by
    change Continuous (fun t => classicalAntiDiscriminantGradientRemainder φ z w t)
    simp_rw [classicalAntiDiscriminantGradientRemainder_eq_sum]
    exact (contDiff_classicalEndpointGradientRemainder φ z w _ _).continuous.add
      (contDiff_classicalEndpointGradientRemainder φ z w _ _).continuous
  rw [hermitianPair_intervalFourierCoefficient _ _ hc.fst hc.snd]
  rw [← intervalIntegral.integral_smul]
  congr 1
  funext t
  exact smul_comm _ _ _

/-- The complete vector coefficient uses the corrected signed free reference in G.6. -/
theorem classicalHermitianAntiDiscriminantGradientCoefficients_lattice {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 1 < q)
    (φ : Curve (ℂ × ℂ)) (z : ℂ) (n k : ℤ) :
    classicalHermitianAntiDiscriminantGradientCoefficients hq φ z ((Real.pi : ℂ)*n) k =
      ∫ t in (0 : ℝ)..1, wave (-k) (2*t) • hermitianPair
        (I • classicalAntiDiscriminantGradient φ z t-(-1 : ℂ)^n • (-wave (2*n) t,wave (-(2*n)) t)) := by
  rw [classicalHermitianAntiDiscriminantGradientCoefficients_apply]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
  dsimp only
  change wave (-k) (2*t) • (I • hermitianPairEquiv.symm _) = _
  rw [← hermitianPairEquiv.symm.map_smul]
  exact congrArg (fun u => wave (-k) (2*t) • hermitianPair u)
    (classicalAntiDiscriminantGradientRemainder_lattice_mul_I φ z n ⟨t,ht'⟩)

end NLS.ZakharovShabat
