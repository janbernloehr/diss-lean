import NLS.Fourier.AbsoluteContinuousCoefficients

/-!
# Classical periodic H¹ and weighted Fourier coefficients

A continuous function on the period-two circle has classical `H¹` regularity
exactly when it has a unique one-derivative `ℓ2` Fourier representative. Here
classical regularity is expressed by absolute continuity on a physical period
and square integrability of the actual derivative.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NLS.Fourier
open ZakharovShabat

/-- Classical Sobolev regularity on one physical period. -/
def HasPeriodicH1Regularity (f : C(AddCircle (2 : ℝ), ℂ)) : Prop :=
  AbsolutelyContinuousOnInterval (fun x : ℝ => f (x : AddCircle (2 : ℝ))) 0 2 ∧
    MemLp (deriv (fun x : ℝ => f (x : AddCircle (2 : ℝ)))) 2 (volume.restrict (Ioc 0 2))

/-- The forward realization satisfies the classical Sobolev conditions. -/
theorem hasPeriodicH1Regularity_sobolevSynthesis (a : ScalarDomain 2) :
    HasPeriodicH1Regularity (sobolevSynthesis (by simp) a) :=
  ⟨absolutelyContinuous_sobolevSynthesis a, memLp_deriv_sobolevSynthesis a⟩

/-- A classical periodic Sobolev function has one-derivative square-summable coefficients. -/
theorem memlp_sobolev_fourierCoeff (f : C(AddCircle (2 : ℝ), ℂ))
    (hf : HasPeriodicH1Regularity f) :
    Memℓp (fun n : ℤ => (Weight.sobolev 1 n : ℂ) * fourierCoeff f n) 2 := by
  have ha : Memℓp (fourierCoeff f) 2 := by
    convert lp.memℓp (continuousFourierCLM f) using 1
    funext n
    exact (continuousFourierCLM_apply f n).symm
  have hfi : IntervalIntegrable (deriv (fun x : ℝ => f (x : AddCircle (2 : ℝ)))) volume 0 2 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
      (hf.2.integrable (by norm_num))
  have hend : f ((2 : ℝ) : AddCircle (2 : ℝ)) = f ((0 : ℝ) : AddCircle (2 : ℝ)) := by
    simpa only [zero_add] using congrArg f (AddCircle.coe_add_period (2 : ℝ) 0)
  have hd := memlp_periodTwoCoefficient hf.2
  have he : periodTwoCoefficient (deriv (fun x : ℝ => f (x : AddCircle (2 : ℝ)))) =
      fun n : ℤ => Complex.I * (Real.pi : ℂ) * n * fourierCoeff f n := by
    funext n
    rw [periodTwoCoefficient_deriv_of_ac_periodic hf.1 hfi hend, periodTwoCoefficient_circle]
  rw [he] at hd
  exact memlp_sobolev_weight_of_derivative ha hd

/-- The weighted coefficients of a classical periodic `H¹` function. -/
def sobolevCoefficients (f : C(AddCircle (2 : ℝ), ℂ)) (hf : HasPeriodicH1Regularity f) :
    ScalarDomain 2 := ⟨fourierCoeff f, memlp_sobolev_fourierCoeff f hf⟩

@[simp] theorem sobolevCoefficients_apply (f : C(AddCircle (2 : ℝ), ℂ))
    (hf : HasPeriodicH1Regularity f) (n : ℤ) :
    (sobolevCoefficients f hf).val n = fourierCoeff f n := rfl

/-- Reconstruction recovers the classical function everywhere, including the endpoints. -/
@[simp] theorem sobolevSynthesis_sobolevCoefficients (f : C(AddCircle (2 : ℝ), ℂ))
    (hf : HasPeriodicH1Regularity f) :
    sobolevSynthesis (by simp) (sobolevCoefficients f hf) = f :=
  (eq_sobolevSynthesis_of_fourierCoeff (by simp) (sobolevCoefficients f hf) f (fun _ => rfl)).symm

/-- Starting from weighted coefficients and taking Fourier integrals is the other inverse. -/
@[simp] theorem sobolevCoefficients_sobolevSynthesis (a : ScalarDomain 2) :
    sobolevCoefficients (sobolevSynthesis (by simp) a)
      (hasPeriodicH1Regularity_sobolevSynthesis a) = a := by
  apply Subtype.ext
  funext n
  simp

/-- Classical periodic `H¹` functions are exactly the uniquely realized weighted `ℓ2` sequences. -/
theorem hasPeriodicH1Regularity_iff_existsUnique (f : C(AddCircle (2 : ℝ), ℂ)) :
    HasPeriodicH1Regularity f ↔ ∃! a : ScalarDomain 2, sobolevSynthesis (by simp) a = f := by
  constructor
  · intro hf
    refine ⟨sobolevCoefficients f hf, sobolevSynthesis_sobolevCoefficients f hf, ?_⟩
    intro a ha
    apply sobolevSynthesis_injective (by simp)
    exact ha.trans (sobolevSynthesis_sobolevCoefficients f hf).symm
  · rintro ⟨a, rfl, _⟩
    exact hasPeriodicH1Regularity_sobolevSynthesis a

end NLS.Fourier
