import NLS.SequenceSpaces.FiniteSourceDensity
import NLS.Fourier.DistributionPeriodicity
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Analytic approximation of original period-two potentials

The decomposition in the opening paragraph of Section 3 uses a real-analytic
potential and a remainder arbitrarily small in the original source norm.
Finite Fourier density supplies this decomposition, with an entire physical
representative, exact Fourier integrals, and equality as actual distributions.
-/

noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory
open scoped ENNReal SchwartzMap
namespace NLS.Fourier

/-- The entire period-two Fourier polynomial of a finite coefficient sequence. -/
def finitePeriodTwoEntire (a : ℤ →₀ ℂ) (z : ℂ) : ℂ :=
  ∑ n ∈ a.support, a n * Complex.exp (((Real.pi : ℂ) * Complex.I * n) * z)

/-- Finite Fourier polynomials are holomorphic on the whole complex plane. -/
theorem analyticOnNhd_finitePeriodTwoEntire (a : ℤ →₀ ℂ) :
    AnalyticOnNhd ℂ (finitePeriodTwoEntire a) univ := by
  intro z _
  unfold finitePeriodTwoEntire
  apply Finset.analyticAt_fun_sum
  intro n _
  exact analyticAt_const.mul (analyticAt_cexp.comp (analyticAt_const.mul analyticAt_id))

/-- Their physical restrictions are real analytic at every real point. -/
theorem realAnalytic_finitePeriodTwoEntire (a : ℤ →₀ ℂ) :
    AnalyticOnNhd ℝ (fun x : ℝ => finitePeriodTwoEntire a x) univ := by
  intro x _
  exact ((analyticOnNhd_finitePeriodTwoEntire a x (mem_univ _)).restrictScalars
    (𝕜 := ℝ)).comp (Complex.ofRealCLM.analyticAt x)

/-- The physical restriction is exactly continuous synthesis of the finite data. -/
theorem finitePeriodTwoEntire_eq_continuousSynthesis (a : ℤ →₀ ℂ) (x : ℝ) :
    finitePeriodTwoEntire a x =
      continuousSynthesis (Coeff.ofFinsupp a) (x : AddCircle (2 : ℝ)) := by
  classical
  rw [continuousSynthesis_apply]
  exact (tsum_eq_sum (s := a.support) (fun n hn => by
    simp [Finsupp.notMem_support_iff.mp hn])).symm

/-- Periodicity holds pointwise, without an even-support assumption. -/
theorem periodic_finitePeriodTwoEntire (a : ℤ →₀ ℂ) :
    Function.Periodic (fun x : ℝ => finitePeriodTwoEntire a x) 2 := by
  intro x
  change finitePeriodTwoEntire a (↑(x+2) : ℂ) = finitePeriodTwoEntire a (x : ℂ)
  rw [finitePeriodTwoEntire_eq_continuousSynthesis,
    finitePeriodTwoEntire_eq_continuousSynthesis,AddCircle.coe_add_period]

/-- Actual normalized period-two Fourier integrals recover every signed mode. -/
theorem periodTwoCoefficient_finitePeriodTwoEntire (a : ℤ →₀ ℂ) (n : ℤ) :
    periodTwoCoefficient (fun x : ℝ => finitePeriodTwoEntire a x) n = a n := by
  simp only [finitePeriodTwoEntire_eq_continuousSynthesis,
    periodTwoCoefficient_continuousSynthesis,Coeff.ofFinsupp_apply]

/-- The same finite potential at any Banach exponent is its physical distribution. -/
theorem distributionSynthesis_ofFinsupp_eq_integral {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (a : ℤ →₀ ℂ) (g : 𝓢(ℝ, ℂ)) :
    distributionSynthesis (Coeff.ofFinsupp (p := p) a) g =
      ∫ x : ℝ, finitePeriodTwoEntire a x * g x := by
  have he : distributionSynthesis (Coeff.ofFinsupp (p := p) a) =
      distributionSynthesis (Coeff.ofFinsupp (p := 1) a) :=
    distributionSynthesis_eq_iff _ _ |>.mpr (fun _ => rfl)
  rw [he,distributionSynthesis_eq_integral_continuousSynthesis]
  simp only [finitePeriodTwoEntire_eq_continuousSynthesis]

/-- Section 3's analytic decomposition in the original finite-exponent pair norm.
The approximant has an entire physical representative. The remainder bound
includes p=1 and permits arbitrary complex, odd and asymmetric Fourier modes. -/
theorem exists_source_analytic_decomposition {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (φ : CoeffPair p) (ε : ℝ) (hε : 0 < ε) :
    ∃ (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (r : CoeffPair p),
      φ = CoeffPair.ofFinsupp a + r ∧ ‖r‖ < ε ∧
      AnalyticOnNhd ℂ (fun z => (finitePeriodTwoEntire a.1 z,
        finitePeriodTwoEntire a.2 z)) univ ∧
      AnalyticOnNhd ℝ (fun x : ℝ => (finitePeriodTwoEntire a.1 x,
        finitePeriodTwoEntire a.2 x)) univ ∧
      Function.Periodic (fun x : ℝ => (finitePeriodTwoEntire a.1 x,
        finitePeriodTwoEntire a.2 x)) 2 ∧
      (∀ n : ℤ, periodTwoCoefficient (fun x : ℝ => finitePeriodTwoEntire a.1 x) n = a.1 n ∧
        periodTwoCoefficient (fun x : ℝ => finitePeriodTwoEntire a.2 x) n = a.2 n) ∧
      (∀ g : 𝓢(ℝ, ℂ),
        distributionSynthesis (CoeffPair.ofFinsupp (p := p) a).fst g =
          ∫ x : ℝ, finitePeriodTwoEntire a.1 x * g x) ∧
      (∀ g : 𝓢(ℝ, ℂ),
        distributionSynthesis (CoeffPair.ofFinsupp (p := p) a).snd g =
          ∫ x : ℝ, finitePeriodTwoEntire a.2 x * g x) := by
  obtain ⟨a,ha⟩ := (CoeffPair.denseRange_ofFinsupp hp).exists_dist_lt φ hε
  refine ⟨a,φ-CoeffPair.ofFinsupp a,by abel,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [dist_eq_norm] using ha
  · intro z hz
    exact (analyticOnNhd_finitePeriodTwoEntire a.1 z hz).prod
      (analyticOnNhd_finitePeriodTwoEntire a.2 z hz)
  · intro x hx
    exact (realAnalytic_finitePeriodTwoEntire a.1 x hx).prod
      (realAnalytic_finitePeriodTwoEntire a.2 x hx)
  · intro x
    exact Prod.ext (periodic_finitePeriodTwoEntire a.1 x)
      (periodic_finitePeriodTwoEntire a.2 x)
  · intro n
    exact ⟨periodTwoCoefficient_finitePeriodTwoEntire a.1 n,
      periodTwoCoefficient_finitePeriodTwoEntire a.2 n⟩
  · exact distributionSynthesis_ofFinsupp_eq_integral a.1
  · exact distributionSynthesis_ofFinsupp_eq_integral a.2

end NLS.Fourier
