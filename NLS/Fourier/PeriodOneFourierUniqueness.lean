import NLS.Fourier.PeriodOneSobolev

/-! # Pointwise uniqueness from period-one Fourier coefficients

Continuous period-one functions with the same actual Fourier integrals
agree everywhere. Even insertion and the vanishing odd coefficients
reduce the result to the existing continuous period-two uniqueness theorem.
-/
noncomputable section
namespace NLS.Fourier
open ZakharovShabat

/-- Actual unit-period Fourier integrals determine a continuous periodic
function at every point of the real line. -/
theorem eq_of_periodOneCoefficient_eq (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hpf : Function.Periodic f 1) (hpg : Function.Periodic g 1)
    (hcoeff : ∀ n : ℤ, periodOneCoefficient f n = periodOneCoefficient g n) : f = g := by
  have hf2 : Function.Periodic f 2 := by simpa using! hpf.nat_mul 2
  have hg2 : Function.Periodic g 2 := by simpa using! hpg.nat_mul 2
  let F : C(AddCircle (2 : ℝ), ℂ) := ⟨hf2.lift,continuous_coinduced_dom.mpr hf⟩
  let G : C(AddCircle (2 : ℝ), ℂ) := ⟨hg2.lift,continuous_coinduced_dom.mpr hg⟩
  have he : F = G := by
    apply continuousFourierCLM_injective
    ext n
    rw [continuousFourierCLM_apply,continuousFourierCLM_apply,
      ← periodTwoCoefficient_circle,← periodTwoCoefficient_circle]
    change periodTwoCoefficient f n = periodTwoCoefficient g n
    by_cases hn : n % 2 = 0
    · have heven : n = 2*(n/2) := by omega
      rw [heven,periodTwoCoefficient_periodic_even f hpf (hf.intervalIntegrable 0 1),
        periodTwoCoefficient_periodic_even g hpg (hg.intervalIntegrable 0 1),hcoeff]
    · have hodd : n = 2*(n/2)+1 := by omega
      rw [hodd,periodTwoCoefficient_periodic_odd f hpf (hf.intervalIntegrable 0 1),
        periodTwoCoefficient_periodic_odd g hpg (hg.intervalIntegrable 0 1)]
  funext x
  exact congrArg (fun H : C(AddCircle (2 : ℝ), ℂ) => H (x : AddCircle (2 : ℝ))) he

/-- An H¹ synthesis equals the continuous periodic function having its
actual original Fourier coefficients. -/
theorem periodOneSobolevSynthesis_eq_of_coefficients (a : ScalarDomain 2) (f : ℝ → ℂ)
    (hf : Continuous f) (hper : Function.Periodic f 1)
    (hcoeff : ∀ n : ℤ, a.val n = periodOneCoefficient f n) :
    (fun x : ℝ => periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ))) = f := by
  apply eq_of_periodOneCoefficient_eq _ f (continuous_periodOneSobolevSynthesis a) hf
    (periodOneSobolevSynthesis_periodic a) hper
  intro n
  rw [periodOneCoefficient_periodOneSobolevSynthesis,hcoeff]

end NLS.Fourier
