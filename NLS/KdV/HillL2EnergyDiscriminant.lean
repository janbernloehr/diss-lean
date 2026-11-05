import NLS.KdV.HillDiscriminantComparison
import NLS.ComplexAnalysis.EntireEvenSquareDescent
import NLS.SequenceSpaces.FiniteCoefficients

/-! # The physical L2 Hill discriminant in the energy variable

The actual L2 monodromy trace is even in frequency, by its checked
continuous-potential identity and finite Fourier density. The shared
Cauchy-circle descent proves joint Banach analyticity in the actual
energy and the L2 potential, including the zero energy.
-/

noncomputable section
open Set
namespace NLS.KdV

theorem continuous_hillL2FrequencyDiscriminant_joint :
    Continuous (fun p : ℂ × Coeff 2 => hillL2FrequencyDiscriminant p.2 p.1) :=
  continuous_iff_continuousAt.mpr
    (fun p => (analyticOnNhd_hillL2FrequencyDiscriminant_joint p (mem_univ _)).continuousAt)

/-- The actual rough physical trace, not merely its zero set, is even. -/
theorem hillL2FrequencyDiscriminant_even (q : Coeff 2) (z : ℂ) :
    hillL2FrequencyDiscriminant q (-z) = hillL2FrequencyDiscriminant q z := by
  have hc (w : ℂ) : Continuous (fun a : Coeff 2 => hillL2FrequencyDiscriminant a w) := by
    have hm : Continuous (fun a : Coeff 2 => (w,a)) := continuous_const.prodMk continuous_id
    simpa only [Function.comp_def] using continuous_hillL2FrequencyDiscriminant_joint.comp hm
  have hfinite (a : ℤ →₀ ℂ) : hillL2FrequencyDiscriminant (Coeff.ofFinsupp (p := 2) a) (-z) =
      hillL2FrequencyDiscriminant (Coeff.ofFinsupp (p := 2) a) z := by
    let Q := Fourier.continuousSynthesis (Coeff.ofFinsupp (p := 1) a)
    have hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) = Coeff.ofFinsupp (p := 2) a := by
      ext k
      simp only [SpectralWeight.toCoeff_apply, hillContinuousCoefficients_apply]
      exact Fourier.fourierCoeff_continuousSynthesis _ k
    change hillL2FrequencyDiscriminant (Coeff.ofFinsupp a) (-z) =
      hillL2FrequencyDiscriminant (Coeff.ofFinsupp a) z
    rw [← hq, hillL2FrequencyDiscriminant_eq_classical, hillL2FrequencyDiscriminant_eq_classical]
    congr 1
    ring
  have he : (fun a : Coeff 2 => hillL2FrequencyDiscriminant a (-z)) =
      (fun a : Coeff 2 => hillL2FrequencyDiscriminant a z) :=
    (Coeff.denseRange_ofFinsupp (p := 2) (by simp)).equalizer (hc (-z)) (hc z) (funext hfinite)
  exact congrFun he q

theorem hillL2FrequencyDiscriminant_eq_of_sq_eq (q : Coeff 2) (z w : ℂ) (he : z^2 = w^2) :
    hillL2FrequencyDiscriminant q z = hillL2FrequencyDiscriminant q w := by
  rcases eq_or_eq_neg_of_sq_eq_sq z w he with h | h
  · rw [h]
  · rw [h, hillL2FrequencyDiscriminant_even]

/-- The actual Hill energy discriminant for a complex L2 coefficient potential.
The value is independent of the root used to represent the energy. -/
def hillL2Discriminant (q : Coeff 2) (lambda : ℂ) : ℂ :=
  hillL2FrequencyDiscriminant q (Complex.sqrt lambda)

theorem hillL2Discriminant_eq_of_sq (q : Coeff 2) (lambda z : ℂ) (hz : z^2 = lambda) :
    hillL2Discriminant q lambda = hillL2FrequencyDiscriminant q z :=
  hillL2FrequencyDiscriminant_eq_of_sq_eq q _ z
    ((ComplexAnalysis.complex_sqrt_sq lambda).trans hz.symm)

@[simp] theorem hillL2Discriminant_sq (q : Coeff 2) (z : ℂ) :
    hillL2Discriminant q (z^2) = hillL2FrequencyDiscriminant q z :=
  hillL2Discriminant_eq_of_sq q (z^2) z rfl

/-- Joint complex analyticity on the full L2 domain, including lambda=0. -/
theorem analyticOnNhd_hillL2Discriminant_joint :
    AnalyticOnNhd ℂ (fun p : ℂ × Coeff 2 => hillL2Discriminant p.2 p.1) univ :=
  ComplexAnalysis.analyticOnNhd_entire_even_square_descent
    (fun p : ℂ × Coeff 2 => hillL2FrequencyDiscriminant p.2 p.1)
    analyticOnNhd_hillL2FrequencyDiscriminant_joint hillL2FrequencyDiscriminant_even
    Complex.sqrt ComplexAnalysis.complex_sqrt_sq

theorem analyticOnNhd_hillL2Discriminant (q : Coeff 2) :
    AnalyticOnNhd ℂ (hillL2Discriminant q) univ := by
  intro lambda _
  exact (analyticOnNhd_hillL2Discriminant_joint (lambda,q) (mem_univ _)).comp
    (f := fun z : ℂ => (z,q)) (analyticAt_id.prod analyticAt_const)

/-- Exact agreement with the already normalized classical Hill discriminant. -/
theorem hillL2Discriminant_eq_classical (Q : C(AddCircle (2 : ℝ), ℂ)) (lambda : ℂ) :
    hillL2Discriminant (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) lambda =
      classicalHillDiscriminant (hillUnitPotentialCurve Q) lambda := by
  obtain ⟨z, rfl⟩ := IsAlgClosed.exists_pow_nat_eq lambda (by norm_num : 0 < 2)
  rw [hillL2Discriminant_sq, hillL2FrequencyDiscriminant_eq_classical]

/-- The exact actual periodic H2 characteristic equation on the full
period-one L2 domain, now expressed in the energy variable. -/
theorem hill_eigenvector_iff_l2Discriminant
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0) (lambda : ℂ) :
    (∃ f : HillSobolevDomain, f ≠ 0 ∧
      hillOperator (SpectralWeight.one.toCoeff q) f = lambda • hillDomainToL2 f) ↔
      hillL2Discriminant (SpectralWeight.one.toCoeff q) lambda ^ 2 = 4 := by
  obtain ⟨z, rfl⟩ := IsAlgClosed.exists_pow_nat_eq lambda (by norm_num : 0 < 2)
  rw [hillL2Discriminant_sq]
  exact hill_eigenvector_iff_l2FrequencyDiscriminant q hq z

theorem hillReduced_zero_iff_l2Discriminant
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (n : ℕ) (hn : 1 ≤ n) (lambda : ℂ) (hz : lambda ∈ reducedHillStrip n)
    (hcut : 8*‖q‖ ≤ (n : ℝ)) :
    hillReducedDeterminant SpectralWeight.one n (q,lambda) = 0 ↔
      hillL2Discriminant (SpectralWeight.one.toCoeff q) lambda ^ 2 = 4 := by
  obtain ⟨z, rfl⟩ := IsAlgClosed.exists_pow_nat_eq lambda (by norm_num : 0 < 2)
  rw [hillL2Discriminant_sq]
  exact hillReduced_zero_iff_l2FrequencyDiscriminant q hq n hn z hz hcut

end NLS.KdV
