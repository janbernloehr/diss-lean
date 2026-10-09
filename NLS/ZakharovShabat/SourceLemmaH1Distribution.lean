import NLS.ZakharovShabat.SourceLemmaH1
import NLS.ZakharovShabat.WeakRiccatiDistribution

/-! # The exact H.1 identity in H⁻¹ and in actual tempered distributions -/
noncomputable section
open NLS.Fourier
open scoped SchwartzMap FourierTransform
namespace NLS.ZakharovShabat

/-- The highest available L² jet, before taking the final weak derivative. -/
def sourceH1TopJet (s : ℕ) (ab : SobolevSource s) : ScalarSobolev 0 :=
  hierarchySobolevInclusion (s-s) 0 (by omega) (hierarchySobolevJet s s le_rfl ab.2)

@[simp] theorem sourceH1TopJet_apply (s : ℕ) (ab : SobolevSource s) (j : ℤ) :
    (sourceH1TopJet s ab).val j = (2*Complex.I*(Real.pi : ℂ)*j)^s*ab.2.val j := by
  simp only [sourceH1TopJet,hierarchySobolevInclusion_apply,hierarchySobolevJet_apply]

/-- The lower-jet polynomial has an actual L² Fourier sequence, even at the H⁰ endpoint. -/
def sourceH1RemainderL2 (s : ℕ) (ab : SobolevSource s) : ScalarSobolev 0 :=
  (WeightedCoeff.weightEquiv (Weight.sobolev (0 : ℕ)) 2).symm
    (Coeff.periodHalve (continuousFourierCLM (sobolevPolynomialField s (nlsRiccatiRemainder (s+1)) ab)))

@[simp] theorem sourceH1RemainderL2_apply (s : ℕ) (ab : SobolevSource s) (j : ℤ) :
    (sourceH1RemainderL2 s ab).val j = sourceH1RemainderCoefficient s ab j := by
  change continuousFourierCLM (sobolevPolynomialField s (nlsRiccatiRemainder (s+1)) ab) (2*j)/
    (Weight.sobolev (0 : ℕ) j : ℂ) = _
  simp [sourceH1RemainderCoefficient]

/-- H.1 as an equality in H⁻¹: the canonical weak density is the leading weak derivative
plus the actual continuous lower-jet polynomial. -/
theorem sourceLemmaH1_weak (s : ℕ) (ab : SobolevSource s) :
    weakSobolevRiccatiDensity s ab =
      -weakRiccatiDerivative (sourceH1TopJet s ab)+weakRiccatiInclusion 0 (sourceH1RemainderL2 s ab) := by
  apply Subtype.ext
  funext j
  simp only [WeightedCoeff.add_val,WeightedCoeff.neg_val,weakRiccatiDerivative_apply,
    sourceH1TopJet_apply,weakRiccatiInclusion_apply,sourceH1RemainderL2_apply]
  rw [sourceLemmaH1,pow_succ]
  ring

/-- The same identity uses the actual tempered-distribution derivative, with period-one normalization. -/
theorem sourceLemmaH1_distribution (s : ℕ) (ab : SobolevSource s) :
    weakRiccatiDistribution (weakSobolevRiccatiDensity s ab) =
      -TemperedDistribution.derivCLM ℂ (distributionSynthesis
        (Coeff.periodDouble (WeightedCoeff.weightEquiv (Weight.sobolev (0 : ℕ)) 2 (sourceH1TopJet s ab))))+
      weakRiccatiDistribution (weakRiccatiInclusion 0 (sourceH1RemainderL2 s ab)) := by
  rw [sourceLemmaH1_weak,map_add,map_neg,weakRiccatiDistribution_derivative]

/-- The represented nonlinear distribution has exactly the actual Fourier integrals of the polynomial field. -/
theorem sourceH1RemainderDistribution_coefficient (s : ℕ) (ab : SobolevSource s) (j : ℤ) :
    weakRiccatiDistribution (weakRiccatiInclusion 0 (sourceH1RemainderL2 s ab)) (coefficientTest (2*j)) =
      periodOneCoefficient (fun x : ℝ => sobolevPolynomialField s (nlsRiccatiRemainder (s+1)) ab
        (x : AddCircle (2 : ℝ))) j := by
  rw [weakRiccatiDistribution_even,weakRiccatiInclusion_apply,sourceH1RemainderL2_apply,
    sourceH1RemainderCoefficient_eq_integral]

end NLS.ZakharovShabat
