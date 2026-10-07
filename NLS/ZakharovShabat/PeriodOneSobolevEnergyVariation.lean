import NLS.ZakharovShabat.PeriodOneSobolevHamiltonian
import NLS.ZakharovShabat.ClassicalNLSEnergyVariation

/-! # Smooth physical variations of the actual H¹ energy

Whenever H¹ coefficients have smooth physical representatives, the Banach
energy agrees with the classical third Hamiltonian. Its complex variations
in either component are the integrals against the corresponding classical
spatial gradient.
-/
noncomputable section
open Set Complex MeasureTheory NLS.Fourier
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- On smooth physical representatives the H¹ energy is the third hierarchy Hamiltonian. -/
theorem periodOneSobolevHamiltonian_eq_classical (a b : ScalarDomain 2)
    (ha : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ))))
    (hb : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis b (x : AddCircle (2 : ℝ)))) :
    periodOneSobolevHamiltonian (a,b) = classicalNLSHamiltonian
      (fun x : ℝ => periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ)))
      (fun x : ℝ => periodOneSobolevSynthesis b (x : AddCircle (2 : ℝ))) 3 := by
  rw [periodOneSobolevHamiltonian_eq_integral,classicalNLSHamiltonian_three _ _ ha hb
    (periodOneSobolevSynthesis_periodic a) (periodOneSobolevSynthesis_periodic b)]

/-- The first H¹ component variation has the classical spatial gradient. -/
theorem hasDerivAt_periodOneSobolevHamiltonian_fst (a b h : ScalarDomain 2)
    (ha : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ))))
    (hb : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis b (x : AddCircle (2 : ℝ))))
    (hh : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis h (x : AddCircle (2 : ℝ)))) :
    HasDerivAt (fun z : ℂ => periodOneSobolevHamiltonian (a+z • h,b))
      (∫ x in (0 : ℝ)..1, periodOneSobolevSynthesis h (x : AddCircle (2 : ℝ)) *
        (classicalNLSEnergyGradient
          (fun y : ℝ => periodOneSobolevSynthesis a (y : AddCircle (2 : ℝ)))
          (fun y : ℝ => periodOneSobolevSynthesis b (y : AddCircle (2 : ℝ)))).1 x) 0 := by
  have he (z : ℂ) : (fun x : ℝ => periodOneSobolevSynthesis (a+z • h) (x : AddCircle (2 : ℝ))) =
      fun x : ℝ => periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ)) +
        z*periodOneSobolevSynthesis h (x : AddCircle (2 : ℝ)) := by
    funext x
    simp only [map_add,map_smul,ContinuousMap.add_apply,ContinuousMap.smul_apply,smul_eq_mul]
  have hf (z : ℂ) := periodOneSobolevHamiltonian_eq_classical (a+z • h) b
    (by rw [he]; exact ha.add (contDiff_const.mul hh)) hb
  simp_rw [hf,he]
  exact hasDerivAt_classicalNLSHamiltonian_three_fst _ _ _ ha hb hh
    (periodOneSobolevSynthesis_periodic a) (periodOneSobolevSynthesis_periodic b)
    (periodOneSobolevSynthesis_periodic h)

/-- The second H¹ component variation has the other classical spatial gradient. -/
theorem hasDerivAt_periodOneSobolevHamiltonian_snd (a b h : ScalarDomain 2)
    (ha : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ))))
    (hb : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis b (x : AddCircle (2 : ℝ))))
    (hh : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis h (x : AddCircle (2 : ℝ)))) :
    HasDerivAt (fun z : ℂ => periodOneSobolevHamiltonian (a,b+z • h))
      (∫ x in (0 : ℝ)..1, periodOneSobolevSynthesis h (x : AddCircle (2 : ℝ)) *
        (classicalNLSEnergyGradient
          (fun y : ℝ => periodOneSobolevSynthesis a (y : AddCircle (2 : ℝ)))
          (fun y : ℝ => periodOneSobolevSynthesis b (y : AddCircle (2 : ℝ)))).2 x) 0 := by
  have he (z : ℂ) : (fun x : ℝ => periodOneSobolevSynthesis (b+z • h) (x : AddCircle (2 : ℝ))) =
      fun x : ℝ => periodOneSobolevSynthesis b (x : AddCircle (2 : ℝ)) +
        z*periodOneSobolevSynthesis h (x : AddCircle (2 : ℝ)) := by
    funext x
    simp only [map_add,map_smul,ContinuousMap.add_apply,ContinuousMap.smul_apply,smul_eq_mul]
  have hf (z : ℂ) := periodOneSobolevHamiltonian_eq_classical a (b+z • h) ha
    (by rw [he]; exact hb.add (contDiff_const.mul hh))
  simp_rw [hf,he]
  exact hasDerivAt_classicalNLSHamiltonian_three_snd _ _ _ ha hb hh
    (periodOneSobolevSynthesis_periodic a) (periodOneSobolevSynthesis_periodic b)
    (periodOneSobolevSynthesis_periodic h)

end NLS.ZakharovShabat
