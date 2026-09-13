import NLS.ZakharovShabat.PhysicalOperator
import NLS.ZakharovShabat.PeriodicParity
import NLS.Fourier.PeriodOneCoefficients
import NLS.FunctionalAnalysis.ComplexAbsoluteContinuity

/-!
# Physical realization of Fourier parity

A parity-supported Sobolev Fourier series has the corresponding multiplier
under translation by one. Its restriction to the unit interval determines the
whole vector, including in the odd sector.
-/

noncomputable section
open Set MeasureTheory NLS.Fourier
open scoped ENNReal
namespace NLS.Fourier

/-- The unit-translation phase depends only on the residue modulo two. -/
theorem wave_one_eq_mod (n : ℤ) : wave n 1 = wave (n % 2) 1 := by
  conv_lhs => rw [show n = 2*(n/2)+n%2 by omega]
  rw [wave_add,wave_even_at_one,one_mul]

/-- Parity support gives the actual pointwise unit-translation law for the continuous Fourier sum. -/
theorem continuousSynthesis_add_one_of_parity (a : Coeff 1) (r : ℤ)
    (ha : ∀ n : ℤ, n%2 ≠ r%2 → a n = 0) (x : ℝ) :
    continuousSynthesis a ((x+1 : ℝ) : AddCircle (2 : ℝ)) =
      wave r 1 * continuousSynthesis a (x : AddCircle (2 : ℝ)) := by
  rw [continuousSynthesis_apply,continuousSynthesis_apply,← tsum_mul_left]
  apply tsum_congr
  intro n
  by_cases hn : n%2 = r%2
  · rw [wave_add_argument,wave_one_eq_mod n,hn,← wave_one_eq_mod r]
    ring
  · rw [ha n hn]
    simp

/-- The original weighted Sobolev representative retains its Fourier parity pointwise. -/
theorem sobolevSynthesis_add_one_of_parity {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (a : ZakharovShabat.ScalarDomain p) (r : ℤ)
    (ha : ∀ n : ℤ, n%2 ≠ r%2 → a.val n = 0) (x : ℝ) :
    sobolevSynthesis hp a ((x+1 : ℝ) : AddCircle (2 : ℝ)) =
      wave r 1 * sobolevSynthesis hp a (x : AddCircle (2 : ℝ)) := by
  exact continuousSynthesis_add_one_of_parity (WeightedCoeff.sobolevToL1CLM p hp a) r (fun n hn => by simpa only [WeightedCoeff.sobolevToL1CLM_apply] using ha n hn) x

end NLS.Fourier
namespace NLS.ZakharovShabat

/-- The original physical domain vector has the endpoint multiplier of its Fourier parity. -/
theorem physicalDomain_add_one_of_parity (a : Domain 2) (r : ℤ)
    (ha : a ∈ domainParitySubspace r) (x : ℝ) :
    physicalDomain a (x+1) = wave r 1 • physicalDomain a x := by
  exact Prod.ext
    (sobolevSynthesis_add_one_of_parity (by simp) a.1 r (fun n hn => (ha n hn).1) x)
    (sobolevSynthesis_add_one_of_parity (by simp) a.2 r (fun n hn => (ha n hn).2) x)

/-- A parity-domain vector is determined by its physical values on the closed unit interval. -/
theorem physicalDomain_eq_zero_on_unit_iff (a : Domain 2) (r : ℤ)
    (ha : a ∈ domainParitySubspace r) :
    EqOn (physicalDomain a) 0 (Icc 0 1) ↔ a = 0 := by
  constructor
  · intro hz
    apply (physicalDomain_eq_zero_ae_iff a).mp
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    by_cases hx1 : x ≤ 1
    · exact hz ⟨hx.1.le,hx1⟩
    · have hshift := physicalDomain_add_one_of_parity a r ha (x-1)
      rw [sub_add_cancel,hz (show x-1 ∈ Icc (0 : ℝ) 1 by constructor <;> linarith [hx.2])] at hshift
      simpa only [Pi.zero_apply,smul_zero] using hshift
  · rintro rfl
    intro x _
    simp [physicalDomain]

/-- The Hilbert-domain physical representative is continuous on the whole real line. -/
theorem continuous_physicalDomain (a : Domain 2) : Continuous (physicalDomain a) := by
  exact ((sobolevSynthesis (by simp) a.1).continuous.comp (by fun_prop)).prodMk
    ((sobolevSynthesis (by simp) a.2).continuous.comp (by fun_prop))

/-- Both original components give an absolutely continuous physical vector on the full period. -/
theorem absolutelyContinuous_physicalDomain (a : Domain 2) :
    AbsolutelyContinuousOnInterval (physicalDomain a) 0 2 := by
  have h₁ := NLS.FunctionalAnalysis.absolutelyContinuousOnInterval_clm
    (absolutelyContinuous_sobolevSynthesis a.1) (ContinuousLinearMap.inl ℝ ℂ ℂ)
  have h₂ := NLS.FunctionalAnalysis.absolutelyContinuousOnInterval_clm
    (absolutelyContinuous_sobolevSynthesis a.2) (ContinuousLinearMap.inr ℝ ℂ ℂ)
  simpa [physicalDomain,ContinuousLinearMap.inl,ContinuousLinearMap.inr,Pi.add_def] using! h₁.add h₂

end NLS.ZakharovShabat
