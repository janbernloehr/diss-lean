import NLS.Poisson.RegularSourceCotangent
import NLS.ZakharovShabat.SourceDiscriminantPoisson

/-!
# Actual discriminant commutation at all finite source exponents

For exponents below two, exponent compatibility identifies the actual
discriminant derivative with the restriction of its Hilbert derivative.
Thus its Fourier coefficients are square summable even though this is
not true of arbitrary continuous cotangents at these exponents. The
regular physical bracket is absolutely convergent and vanishes for
every complex source and every pair of spectral parameters.
-/

noncomputable section
open Set Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- Exponent compatibility holds for the actual full source derivative. -/
theorem sourceDiscriminantCotangent_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hq1 : 1 < q) (hpq : p ≤ q)
    (z : ℂ) (φ : CoeffPair p) :
    sourceDiscriminantCotangent hp z φ =
      (sourceDiscriminantCotangent hq z (CoeffPair.exponentInclusion hpq φ)).comp
        (CoeffPair.exponentInclusion hpq) := by
  have heq : (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) z) =
      (fun ψ : CoeffPair q => canonicalDiscriminant hq (periodOnePotential ψ) z) ∘
        CoeffPair.exponentInclusion hpq := by
    funext ψ
    exact sourceDiscriminant_exponent hp hq hpq ψ z
  unfold sourceDiscriminantCotangent
  rw [heq, fderiv_comp φ
    ((analyticOnNhd_sourceDiscriminant_section hq hq1 z _ (mem_univ _)).differentiableAt)
    (CoeffPair.exponentInclusion hpq).differentiableAt, ContinuousLinearMap.fderiv]

/-- The regular cotangent is constructed from the actual derivative.
Below two, its Hilbert coefficients come from the proved restriction. -/
def sourceDiscriminantRegularCotangent (hp : p ≠ ⊤) (z : ℂ) (φ : CoeffPair p) :
    RegularSourceCotangent p :=
  if h2p : (2 : ℝ≥0∞) ≤ p then
    RegularSourceCotangent.ofCotangent h2p (sourceDiscriminantCotangent hp z φ)
  else
    (RegularSourceCotangent.ofCotangent (le_refl (2 : ℝ≥0∞))
      (sourceDiscriminantCotangent (by simp) z
        (CoeffPair.exponentInclusion (le_of_not_ge h2p) φ))).restrict (le_of_not_ge h2p)

@[simp] theorem sourceDiscriminantRegularCotangent_toCotangent
    (hp : p ≠ ⊤) (z : ℂ) (φ : CoeffPair p) :
    (sourceDiscriminantRegularCotangent hp z φ).toCotangent = sourceDiscriminantCotangent hp z φ := by
  unfold sourceDiscriminantRegularCotangent
  split
  · rfl
  · exact (sourceDiscriminantCotangent_exponent hp (by simp) (by norm_num) _ z φ).symm

/-- The full Hilbert coefficient pair, not merely its bracket, is
independent of the source exponent. -/
theorem sourceDiscriminantRegularCotangent_coefficients_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hq1 : 1 < q) (hpq : p ≤ q)
    (φ : CoeffPair p) (z : ℂ) :
    (sourceDiscriminantRegularCotangent hp z φ).coefficients =
      (sourceDiscriminantRegularCotangent hq z (CoeffPair.exponentInclusion hpq φ)).coefficients := by
  exact RegularSourceCotangent.coefficients_eq_of_toCotangent_eq
    (sourceDiscriminantRegularCotangent hp z φ)
    ((sourceDiscriminantRegularCotangent hq z (CoeffPair.exponentInclusion hpq φ)).restrict hpq)
    (by simpa only [RegularSourceCotangent.restrict, sourceDiscriminantRegularCotangent_toCotangent]
      using sourceDiscriminantCotangent_exponent hp hq hq1 hpq z φ)

/-- The regularity holds analytically in the Hilbert coefficient norm,
jointly in spectral parameter and source, throughout `1 < p < ∞`. -/
theorem analyticOnNhd_sourceDiscriminantRegularCoefficients_joint
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    AnalyticOnNhd ℂ (fun t : ℂ × CoeffPair p =>
      (sourceDiscriminantRegularCotangent hp t.1 t.2).coefficients) univ := by
  intro t _
  by_cases h2p : (2 : ℝ≥0∞) ≤ p
  · simp only [sourceDiscriminantRegularCotangent, dif_pos h2p,
      RegularSourceCotangent.ofCotangent]
    exact ((CoeffPair.cotangentCoefficients h2p).analyticAt _).comp
      (analyticOnNhd_sourceDiscriminantCotangent_joint hp hp1 t (mem_univ _))
  · simp only [sourceDiscriminantRegularCotangent, dif_neg h2p,
      RegularSourceCotangent.ofCotangent, RegularSourceCotangent.restrict]
    exact ((CoeffPair.cotangentCoefficients (le_refl (2 : ℝ≥0∞))).analyticAt _).comp
      ((analyticOnNhd_sourceDiscriminantCotangent_joint (p := 2) (by simp) (by norm_num)
        (t.1, CoeffPair.exponentInclusion (le_of_not_ge h2p) t.2) (mem_univ _)).comp
        (f := fun u : ℂ × CoeffPair p => (u.1, CoeffPair.exponentInclusion (le_of_not_ge h2p) u.2))
        (analyticAt_fst.prod (((CoeffPair.exponentInclusion (le_of_not_ge h2p)).analyticAt _).comp analyticAt_snd)))

/-- The bracket is independent of which source exponent represents
the potential; this statement also covers restrictions below two. -/
theorem sourceDiscriminantRegularCotangent_bivector_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hq1 : 1 < q) (hpq : p ≤ q)
    (φ : CoeffPair p) (z w : ℂ) :
    (sourceDiscriminantRegularCotangent hp z φ).bivector
      (sourceDiscriminantRegularCotangent hp w φ) =
    (sourceDiscriminantRegularCotangent hq z (CoeffPair.exponentInclusion hpq φ)).bivector
      (sourceDiscriminantRegularCotangent hq w (CoeffPair.exponentInclusion hpq φ)) := by
  rw [← RegularSourceCotangent.bivector_restrict hpq]
  apply RegularSourceCotangent.bivector_congr <;>
    simp only [RegularSourceCotangent.restrict, sourceDiscriminantRegularCotangent_toCotangent] <;>
    exact sourceDiscriminantCotangent_exponent hp hq hq1 hpq _ φ

/-- Actual discriminant commutation on the full range `1 < p < ∞`.
No real-type, finite-support, or assumed gradient condition is needed. -/
theorem sourceDiscriminantRegularCotangent_bivector_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (z w : ℂ) :
    (sourceDiscriminantRegularCotangent hp z φ).bivector
      (sourceDiscriminantRegularCotangent hp w φ) = 0 := by
  unfold sourceDiscriminantRegularCotangent
  split
  · exact sourceBracket_discriminants_eq_zero hp hp1 _ φ z w
  · exact sourceBracket_discriminants_eq_zero (by simp) (by norm_num) (by norm_num) _ z w

/-- Absolute convergence of the Fourier formula for the actual source
derivatives, including at exponents strictly below two. -/
theorem sourceDiscriminantCotangent_pairing_summable_norm
    (hp : p ≠ ⊤) (φ : CoeffPair p) (z w : ℂ) :
    Summable (fun n : ℤ => ‖
      sourceDiscriminantCotangent hp z φ (CoeffPair.inlCLM (lp.single p n 1)) *
        sourceDiscriminantCotangent hp w φ (CoeffPair.inrCLM (lp.single p (-n) 1)) -
      sourceDiscriminantCotangent hp z φ (CoeffPair.inrCLM (lp.single p n 1)) *
        sourceDiscriminantCotangent hp w φ (CoeffPair.inlCLM (lp.single p (-n) 1))‖) := by
  simpa only [sourceDiscriminantRegularCotangent_toCotangent] using
    (sourceDiscriminantRegularCotangent hp z φ).summable_norm
      (sourceDiscriminantRegularCotangent hp w φ)

/-- The literal physical Fourier Poisson bracket of the actual
discriminants vanishes throughout the full finite exponent range. -/
theorem sourceDiscriminantCotangent_fourier_bracket_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (z w : ℂ) :
    -I * (∑' n : ℤ,
      (sourceDiscriminantCotangent hp z φ (CoeffPair.inlCLM (lp.single p n 1)) *
        sourceDiscriminantCotangent hp w φ (CoeffPair.inrCLM (lp.single p (-n) 1)) -
      sourceDiscriminantCotangent hp z φ (CoeffPair.inrCLM (lp.single p n 1)) *
        sourceDiscriminantCotangent hp w φ (CoeffPair.inlCLM (lp.single p (-n) 1)))) = 0 := by
  have h := (sourceDiscriminantRegularCotangent hp z φ).bivector_eq_tsum
    (sourceDiscriminantRegularCotangent hp w φ)
  rw [sourceDiscriminantRegularCotangent_bivector_eq_zero hp hp1 φ z w] at h
  simpa only [sourceDiscriminantRegularCotangent_toCotangent] using h.symm

end NLS.ZakharovShabat
