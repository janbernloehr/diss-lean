import NLS.Fourier.AbelStripWitness
import NLS.ZakharovShabat.NormalizedWeightedSourceTopology

noncomputable section
set_option autoImplicit false
open Set Filter Topology Complex MeasureTheory
open scoped ENNReal ContDiff
namespace NLS.ZakharovShabat
open NLS.Fourier

/-- An actual original Hilbert source with zero first component and the geometric physical second component. -/
def section23AbelCounterexampleSource : CoeffPair 2 :=
  WithLp.toLp 2 (0,⟨geometricPeriodOneCoefficients (1/3),
    (geometricPeriodOneCoefficients_mem (1/3) (by norm_num)).of_exponent_ge (by norm_num)⟩)

@[simp] theorem section23AbelCounterexampleSource_fst (n : ℤ) :
    section23AbelCounterexampleSource.fst n = 0 := rfl

/-- The source's raw second coefficients are actual Fourier integrals of the physical witness. -/
theorem section23AbelCounterexampleSource_snd (n : ℤ) :
    section23AbelCounterexampleSource.snd n =
      periodOneCoefficient (fun x : ℝ => section23StripWitness x) n :=
  (section23StripWitness_coefficient n).symm

/-- The physical Hilbert source does not lie in the image of the original Abel-weight decoder. -/
theorem section23AbelCounterexampleSource_not_weighted :
    section23AbelCounterexampleSource ∉
      range (normalizedWeightedSource (p := 2) section23AbelWitnessWeight) := by
  rintro ⟨a,ha⟩
  apply section23StripWitness_not_abel
  have he : (fun n : ℤ => (section23AbelWitnessWeight (2*n):ℂ)*
      periodOneCoefficient (fun x : ℝ => section23StripWitness x) n) = ⇑a.snd := by
    funext n
    have h := congrArg (fun φ : CoeffPair 2 => φ.snd n) ha
    rw [normalizedWeightedSource_snd,section23AbelCounterexampleSource_snd] at h
    rw [← h]
    field_simp [section23AbelWitnessWeight.toWeight.complex_ne_zero (2*n)]
  rw [he]
  exact lp.memℓp a.snd

/-- The printed strip condition, with actual boundary traces and a physical source,
does not imply membership in the literal original Abel space. -/
theorem exists_source_section23PrintedStrip_counterexample :
    ∃ φ : CoeffPair 2, ∃ f : ℂ → ℂ,
      (∀ n, φ.fst n = 0 ∧ φ.snd n = periodOneCoefficient (fun x : ℝ => f x) n) ∧
      AnalyticOnNhd ℂ f {z | |z.im| ≤ Real.log 2/(2*Real.pi)} ∧
      (∀ y : ℝ, |y| ≤ Real.log 2/(2*Real.pi) →
        Function.Periodic (fun x : ℝ => f (x+I*y)) 1 ∧
        ContDiff ℝ ∞ (fun x : ℝ => f (x+I*y)) ∧
        MemLp (fun x : ℝ => f (x+I*y)) 2 (volume.restrict (Ioc 0 1))) ∧
      φ ∉ range (normalizedWeightedSource (p := 2) section23AbelWitnessWeight) := by
  exact ⟨section23AbelCounterexampleSource,section23StripWitness,
    fun n => ⟨section23AbelCounterexampleSource_fst n,section23AbelCounterexampleSource_snd n⟩,
    section23StripWitness_analytic_closed_strip,
    fun y hy => ⟨section23StripWitness_trace_periodic y,section23StripWitness_trace_smooth y hy,
      section23StripWitness_trace_memLp y hy⟩,
    section23AbelCounterexampleSource_not_weighted⟩

end NLS.ZakharovShabat
