import NLS.Fourier.PrintedChirpContinuous
import NLS.Fourier.PeriodicFourierLebesgueSeries

/-! # The literal continuous witness displayed in the proof of A.5 -/
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped ENNReal
namespace NLS.Fourier

/-- The continuous printed witness in real physical coordinates. -/
def printedChirpFunction (x : ℝ) : ℂ := printedChirpContinuous (x : AddCircle (2 : ℝ))

theorem continuous_printedChirpFunction : Continuous printedChirpFunction :=
  printedChirpContinuous.continuous.comp (AddCircle.continuous_mk' (2 : ℝ))

theorem periodic_printedChirpFunction : Function.Periodic printedChirpFunction 2 := by
  intro x
  simp only [printedChirpFunction,AddCircle.coe_add_period]

/-- The ordinary cutoff agrees with the prescribed lower index two. -/
theorem printedChirpPartialSum_eq_Icc (N : ℕ) :
    printedChirpPartialSum (N+1) = ∑ n ∈ Finset.Icc 2 N, printedChirpTerm n := by
  symm
  apply Finset.sum_subset
  · intro n hn
    simp only [Finset.mem_Icc,Finset.mem_range] at hn ⊢
    omega
  · intro n hn hout
    have hn2 : n < 2 := by
      simp only [Finset.mem_range,Finset.mem_Icc] at hn hout
      omega
    simp [printedChirpTerm,printedChirpCoefficient,show ¬(2 : ℤ) ≤ n by omega]

/-- Exact physical exponential factors, without replacing the printed phase. -/
theorem printedChirpTerm_coe_original (n : ℕ) (hn : 2 ≤ n) (x : ℝ) :
    printedChirpTerm n (x : AddCircle (2 : ℝ)) =
      (Complex.exp (Complex.I*((n : ℝ)*Real.log n)) /
        ((Real.sqrt n*(Real.log n)^2 : ℝ) : ℂ)) *
          Complex.exp (Complex.I*((n : ℝ)*Real.pi*x)) := by
  simp only [printedChirpTerm,ContinuousMap.coe_smul,Pi.smul_apply,smul_eq_mul,
    printedChirpCoefficient,if_pos (show (2 : ℤ) ≤ n by exact_mod_cast hn),fourier_coe_apply,
    Int.cast_natCast,Complex.ofReal_ofNat]
  congr 1
  congr 1
  push_cast
  ring

/-- The exact printed positive-index partial sums converge uniformly on all real x. -/
theorem tendstoUniformly_printedChirp_original :
    TendstoUniformly (fun (N : ℕ) (x : ℝ) => ∑ n ∈ Finset.Icc 2 N,
      (Complex.exp (Complex.I*((n : ℝ)*Real.log n)) /
        ((Real.sqrt n*(Real.log n)^2 : ℝ) : ℂ)) *
          Complex.exp (Complex.I*((n : ℝ)*Real.pi*x))) printedChirpFunction atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have ht := Metric.tendstoUniformly_iff.mp tendstoUniformly_printedChirpPartialSum_real ε hε
  have ht' := (tendsto_add_atTop_nat 1).eventually ht
  filter_upwards [ht'] with N hN
  intro x
  have he : printedChirpPartialSum (N+1) (x : AddCircle (2 : ℝ)) =
      ∑ n ∈ Finset.Icc 2 N,
        (Complex.exp (Complex.I*((n : ℝ)*Real.log n)) /
          ((Real.sqrt n*(Real.log n)^2 : ℝ) : ℂ)) *
            Complex.exp (Complex.I*((n : ℝ)*Real.pi*x)) := by
    rw [printedChirpPartialSum_eq_Icc,ContinuousMap.sum_apply]
    exact Finset.sum_congr rfl fun n hn => printedChirpTerm_coe_original n
      (Finset.mem_Icc.mp hn).1 x
  simpa only [printedChirpFunction,he] using hN x

/-- Actual normalized interval Fourier integrals recover the printed coefficients. -/
theorem periodTwoCoefficient_printedChirpFunction (n : ℤ) :
    periodTwoCoefficient printedChirpFunction n = printedChirpCoefficient n := by
  exact (periodTwoCoefficient_circle printedChirpContinuous n).trans
    (fourierCoeff_printedChirpContinuous n)

/-- The source's explicit continuous witness lies in no Banach Fourier-Lebesgue space below two. -/
theorem memlp_periodTwoCoefficient_printedChirpFunction_iff
    {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    Memℓp (periodTwoCoefficient printedChirpFunction) p ↔ 2 ≤ p := by
  simp only [show periodTwoCoefficient printedChirpFunction = printedChirpCoefficient from
    funext periodTwoCoefficient_printedChirpFunction,memlp_printedChirpCoefficient_iff]

/-- The exact threshold also holds in the source's original distribution-based spaces. -/
theorem printedChirpContinuous_mem_original_iff {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    SmoothPeriodicTest.Distribution.ofContinuous printedChirpContinuous ∈
      periodicFourierLebesgueSubmodule Weight.one p ↔ 2 ≤ p := by
  change Memℓp (fun k => (Weight.one k : ℂ)*
    SmoothPeriodicTest.Distribution.ofContinuous printedChirpContinuous (SmoothPeriodicTest.mode (-k))) p ↔ 2 ≤ p
  simpa only [Weight.one_apply,Complex.ofReal_one,one_mul,
    SmoothPeriodicTest.Distribution.ofContinuous_coefficient] using
    (memlp_fourierCoeff_printedChirpContinuous_iff (p := p))

end NLS.Fourier
