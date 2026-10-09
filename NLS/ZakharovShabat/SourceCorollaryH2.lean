import NLS.ZakharovShabat.SobolevTopJetPhysical
import NLS.ZakharovShabat.SobolevOddHamiltonianReal
import NLS.ZakharovShabat.SobolevSourceSmoothDensity

/-! # Corollary H.2 on the full real Sobolev space

One polynomial, chosen before the source, satisfies the printed jet order,
total degree and field balance. The leading term is the actual physical
square integral of the highest weak derivative, including nonsmooth inputs.
-/
noncomputable section
open NLS.Fourier NLS.DifferentialPolynomial MeasureTheory Set
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- All printed algebraic restrictions hold for the same chosen polynomial. -/
theorem sourceH2Polynomial_properties (m : ℕ) (hm : 1 ≤ m) :
    JetOrderLE (nlsOddReducedPolynomial m hm) (m-1) ∧
    (nlsOddReducedPolynomial m hm).IsWeightedHomogeneous totalWeight (2*(m : ℤ)+2) ∧
    (nlsOddReducedPolynomial m hm).IsWeightedHomogeneous fieldCharge 0 := by
  have h := Classical.choose_spec (exists_classicalNLSHamiltonian_odd_reduced_polynomial m hm)
  exact ⟨h.1,h.2.1,h.2.2.1⟩

/-- Bilinear Parseval for the highest derivatives, with no extra smoothness assumption. -/
theorem sobolevOddKinetic_eq_physical_integral (m : ℕ) (hm : 1 ≤ m) (ab : SobolevSource m) :
    sobolevOddKinetic m ab = ∫ x in (0 : ℝ)..1,
      sobolevTopJetPhysical m hm ab.1 x*sobolevTopJetPhysical m hm ab.2 x := by
  have h := tsum_bilinear_unitFourierCoefficient_of_memLp
    (memLp_sobolevTopJetPhysical m hm ab.1) (memLp_sobolevTopJetPhysical m hm ab.2)
  have he (f : ℝ → ℂ) (n : ℤ) : unitFourierCoefficient f n = periodOneCoefficient f n :=
    unitFourierCoefficient_eq_fourierCoeffOn f n
  simpa only [he,periodOneCoefficient_sobolevTopJetPhysical,sobolevOddKinetic,
    Coeff.dualPairing_apply,Coeff.reflection_apply] using h

/-- The physical integral formula extends to the entire complex H^m source. -/
theorem sobolevOddHamiltonian_eq_physical_integral (m : ℕ) (hm : 1 ≤ m) (ab : SobolevSource m) :
    sobolevOddHamiltonian m hm ab = ∫ x in (0 : ℝ)..1,
      sobolevTopJetPhysical m hm ab.1 x*sobolevTopJetPhysical m hm ab.2 x+
        sobolevPolynomialField m (nlsOddReducedPolynomial m hm) ab (x : AddCircle (2 : ℝ)) := by
  rw [sobolevOddHamiltonian,sobolevOddKinetic_eq_physical_integral m hm,
    sobolevPolynomialMean_eq_physical_integral]
  symm
  apply intervalIntegral.integral_add
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
      ((memLp_sobolevTopJetPhysical m hm ab.1).integrable_mul (memLp_sobolevTopJetPhysical m hm ab.2))
  · exact ((sobolevPolynomialField m (nlsOddReducedPolynomial m hm) ab).continuous.comp
      continuous_quotient_mk').intervalIntegrable 0 1

/-- H.2's single physical integral, on every real H^m source. -/
theorem sourceCorollaryH2_integral (m : ℕ) (hm : 1 ≤ m)
    (a : realTypeHigherSobolevSourceLocus m) :
    sobolevOddHamiltonian m hm a.val = ∫ x in (0 : ℝ)..1,
      (‖sobolevTopJetPhysical m hm a.val.1 x‖^2 : ℝ)+
        sobolevPolynomialField m (nlsOddReducedPolynomial m hm) a.val (x : AddCircle (2 : ℝ)) := by
  rw [sobolevOddHamiltonian_real_decomposition,
    ← integral_sq_sobolevTopJetPhysical m hm,sobolevPolynomialMean_eq_physical_integral,
    ← intervalIntegral.integral_ofReal]
  symm
  apply intervalIntegral.integral_add
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
      ((memLp_sobolevTopJetPhysical m hm a.val.1).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).ofReal
  · exact ((sobolevPolynomialField m (nlsOddReducedPolynomial m hm) a.val).continuous.comp
      continuous_quotient_mk').intervalIntegrable 0 1

/-- The source quantifier order: for each m, one graded polynomial works for all real H^m inputs. -/
theorem sourceCorollaryH2 (m : ℕ) (hm : 1 ≤ m) :
    ∃ q : DifferentialPolynomial.Polynomial, JetOrderLE q (m-1) ∧
      q.IsWeightedHomogeneous totalWeight (2*(m : ℤ)+2) ∧
      q.IsWeightedHomogeneous fieldCharge 0 ∧
      ∀ a : realTypeHigherSobolevSourceLocus m,
        sobolevOddHamiltonian m hm a.val = ∫ x in (0 : ℝ)..1,
          (‖sobolevTopJetPhysical m hm a.val.1 x‖^2 : ℝ)+
            sobolevPolynomialField m q a.val (x : AddCircle (2 : ℝ)) :=
  ⟨nlsOddReducedPolynomial m hm,(sourceH2Polynomial_properties m hm).1,
    (sourceH2Polynomial_properties m hm).2.1,(sourceH2Polynomial_properties m hm).2.2,
    sourceCorollaryH2_integral m hm⟩

/-- The full Sobolev Hamiltonian is determined by the original smooth physical hierarchy,
assuming continuity only, without spectral or real-type hypotheses. -/
theorem sobolevOddHamiltonian_unique_continuous (m : ℕ) (hm : 1 ≤ m)
    (F : SobolevSource m → ℂ) (hF : Continuous F)
    (hclassical : ∀ (ab : SobolevSource m) (f g : ℝ → ℂ),
      ContDiff ℝ ∞ f → ContDiff ℝ ∞ g → Function.Periodic f 1 → Function.Periodic g 1 →
      (∀ j, ab.1.val j = periodOneCoefficient f j) →
      (∀ j, ab.2.val j = periodOneCoefficient g j) → F ab = classicalNLSHamiltonian f g (2*m+1)) :
    F = sobolevOddHamiltonian m hm := by
  apply eq_of_continuous_of_smooth_sobolevSource m F _ hF (continuous_sobolevOddHamiltonian m hm)
  intro ab f g hf hg hpf hpg ha hb
  exact (hclassical ab f g hf hg hpf hpg ha hb).trans
    (sobolevOddHamiltonian_eq_classical m hm ab f g hf hg hpf hpg ha hb).symm

end NLS.ZakharovShabat
