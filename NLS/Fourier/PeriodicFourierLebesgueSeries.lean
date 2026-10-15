import NLS.Fourier.PeriodicFourierLebesgueSpace
/-! # Actual Fourier polynomials and distributional convergence

Finite coefficient truncations equal integration against the physical continuous
trigonometric polynomial. For every Banach exponent, including infinity, these
polynomials converge against every original smooth periodic test and in the
pointwise topology of the actual tempered realization.
-/
noncomputable section
open scoped ENNReal SchwartzMap
open Filter Topology Set MeasureTheory
namespace NLS.Fourier
open SmoothPeriodicTest
variable {L : ℝ} [Fact (0 < L)]

theorem intervalFourierCoefficient_pullback_circle (g : C(AddCircle L,ℂ)) (n : ℤ) :
    intervalFourierCoefficient L (fun x : ℝ => g (x : AddCircle L)) n = fourierCoeff g n := by
  rw [intervalFourierCoefficient_eq_fourierCoeffOn (Fact.out : 0 < L),
    fourierCoeffOn_eq_integral,fourierCoeff_eq_intervalIntegral _ _ 0]
  simp only [fourier_coe_apply,zero_add,sub_zero,smul_eq_mul,Complex.real_smul]

namespace SmoothPeriodicTest.Distribution

def ofContinuous (g : C(AddCircle L,ℂ)) : Distribution L :=
  ofL1 (fun x : ℝ => g (x : AddCircle L))
    ((show Continuous (fun x : ℝ => g (x : AddCircle L)) by fun_prop).intervalIntegrable 0 L)

theorem ofContinuous_coefficient (g : C(AddCircle L,ℂ)) (n : ℤ) :
    ofContinuous g (mode (-n)) = fourierCoeff g n := by
  rw [ofContinuous,ofL1_coefficient,intervalFourierCoefficient_pullback_circle]

theorem ofContinuous_injective : Function.Injective (ofContinuous (L := L)) := by
  intro f g h
  apply ContinuousMap.toLp_injective (p := 2) AddCircle.haarAddCircle (𝕜 := ℂ)
  apply fourierBasis.repr.injective
  ext n
  have hc := congrArg (fun u : Distribution L => u (mode (-n))) h
  simpa only [fourierBasis_repr,fourierCoeff_toLp,ofContinuous_coefficient] using hc

theorem ofContinuous_fourier_coefficient (k n : ℤ) :
    ofContinuous (fourier k : C(AddCircle L,ℂ)) (mode (-n)) = if n = k then 1 else 0 := by
  rw [ofContinuous_coefficient,fourierCoeff_fourier]
  simp [Pi.single_apply,eq_comm]

end SmoothPeriodicTest.Distribution

def continuousFourierPolynomial (S : Finset ℤ) (a : ℤ → ℂ) : C(AddCircle L,ℂ) :=
  ∑ n ∈ S, a n • fourier n

theorem continuousFourierPolynomial_coefficient (S : Finset ℤ) (a : ℤ → ℂ) (n : ℤ) :
    fourierCoeff (continuousFourierPolynomial (L := L) S a) n = if n ∈ S then a n else 0 := by
  classical
  have hi (k : ℤ) : Integrable (fun x : AddCircle L => a k * fourier k x) AddCircle.haarAddCircle :=
    (show Continuous (fun x : AddCircle L => a k * fourier k x) by fun_prop).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change fourierCoeff (⇑(∑ k ∈ S, a k • (fourier k : C(AddCircle L,ℂ)))) n = _
  rw [ContinuousMap.coe_sum,fourierCoeff.sum]
  · simp [ContinuousMap.coe_smul,fourierCoeff.const_smul,fourierCoeff_fourier,Pi.single_apply]
  · intro k _
    exact hi k
end NLS.Fourier

namespace NLS.Fourier.PeriodicFourierLebesgue
open SmoothPeriodicTest
variable {L : ℝ} [Fact (0 < L)]
variable (w : Weight) (p : ℝ≥0∞) [Fact (1 ≤ p)]

theorem truncate_eq_ofContinuous (hw : w.HasTemperedInverse) (S : Finset ℤ) (u : PeriodicFourierLebesgue L w p) :
    (truncate w p hw S u).val = Distribution.ofContinuous
      (continuousFourierPolynomial S (fun n => u.val (mode (-n)))) := by
  apply Distribution.ext_coefficients
  intro n
  rw [truncate_coefficient,Distribution.ofContinuous_coefficient,continuousFourierPolynomial_coefficient]



theorem toTempered_eq_synthesis (hw : w.HasTemperedInverse) (u : PeriodicFourierLebesgue L w p) :
    u.val.toTempered = arbitraryPeriodDistributionSynthesis L Fact.out w hw (coefficientsLM w p u) := by
  apply periodicDistribution_ext_arbitraryPeriod L Fact.out u.val.toTempered_periodic
    (arbitraryPeriodDistributionSynthesis_periodic L Fact.out w hw (coefficientsLM w p u))
  intro n
  rw [Distribution.toTempered_coefficient,arbitraryPeriodDistributionSynthesis_coefficient]
  rfl

theorem coefficientsLM_truncate (hw : w.HasTemperedInverse) (S : Finset ℤ) (u : PeriodicFourierLebesgue L w p) :
    coefficientsLM w p (truncate w p hw S u) = WeightedCoeff.truncate w p S (coefficientsLM w p u) := by
  change coefficientsEquiv w p hw (truncate w p hw S u) = _
  rw [truncate,LinearEquiv.apply_symm_apply]

theorem tendsto_toTempered_truncate (hw : w.HasTemperedInverse) (u : PeriodicFourierLebesgue L w p) :
    Tendsto (fun S : Finset ℤ => (truncate w p hw S u).val.toTempered) atTop (𝓝 u.val.toTempered) := by
  simp only [toTempered_eq_synthesis w p hw,coefficientsLM_truncate]
  exact tendsto_arbitraryPeriodDistributionSynthesis_truncate L Fact.out w hw (coefficientsLM w p u)

theorem tendsto_truncate_action (hw : w.HasTemperedInverse) (u : PeriodicFourierLebesgue L w p)
    (f : SmoothPeriodicTest L) :
    Tendsto (fun S : Finset ℤ => (truncate w p hw S u).val f) atTop (𝓝 (u.val f)) := by
  have h := PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.mp (tendsto_toTempered_truncate w p hw u)
    (windowCLM (periodCoefficientTest L Fact.out 0) f)
  have he (v : Distribution L) : v.toTempered (windowCLM (periodCoefficientTest L Fact.out 0) f) = v f :=
    congrArg (fun v : Distribution L => v f) (Distribution.ofTempered_toTempered v)
  simpa only [he] using h

end NLS.Fourier.PeriodicFourierLebesgue
