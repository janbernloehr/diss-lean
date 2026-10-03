import NLS.ZakharovShabat.ClassicalDiscriminantGradientEnergy
import NLS.ZakharovShabat.FiniteSourceDiscriminantGradient
import NLS.ZakharovShabat.SourceDiscriminantEnergyBound
import NLS.Fourier.UnitIntervalC1FourierLebesgue
import NLS.SequenceSpaces.DominatedTails

/-! # Uniform Fourier decay of the actual Hilbert discriminant cotangent

Exact finite-source realization identifies the cotangent coordinates with
physical gradient coefficients. Density extends their energy bound to every
complex Hilbert source. Thus bounded source and spectral balls share one
inverse-bracket majorant, independently of physical supremum norms.
-/

noncomputable section
open Set Complex MeasureTheory Filter NLS.Fourier
open scoped ENNReal Topology
namespace NLS.ZakharovShabat
local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

private theorem unitFourierCoefficient_eq_interval (f : ℝ → ℂ) (n : ℤ) :
    unitFourierCoefficient f n = intervalFourierCoefficient 1 f n := by
  simp only [unitFourierCoefficient,intervalFourierCoefficient,div_one,
    Complex.ofReal_one,one_mul]
  apply intervalIntegral.integral_congr
  intro s _
  apply congrArg (fun w : ℂ => f s * Complex.exp w)
  push_cast
  ring

/-- Both actual cotangent coordinate sequences satisfy the same energy
bound on the entire complex Hilbert source space. -/
theorem norm_sourceDiscriminantCotangent_coefficient_le_energy
    (φ : CoeffPair 2) (z : ℂ) (n : ℤ) :
    ‖(CoeffPair.cotangentCoefficients (by norm_num)
      (sourceDiscriminantCotangent (by simp) z φ)).1 n‖ ≤
        (8*(Real.exp (‖z‖+1+‖φ‖^2))^3*(‖z‖+2+‖φ‖^2))/(1+|(n : ℝ)|) ∧
    ‖(CoeffPair.cotangentCoefficients (by norm_num)
      (sourceDiscriminantCotangent (by simp) z φ)).2 n‖ ≤
        (8*(Real.exp (‖z‖+1+‖φ‖^2))^3*(‖z‖+2+‖φ‖^2))/(1+|(n : ℝ)|) := by
  have hF : Continuous (fun ψ : CoeffPair 2 => sourceDiscriminantCotangent (by simp) z ψ) := by
    apply continuous_iff_continuousAt.mpr
    intro ψ
    exact ((analyticOnNhd_sourceDiscriminantCotangent_joint (by simp) (by norm_num)
      (z,ψ) (mem_univ _)).comp (f := fun χ : CoeffPair 2 => (z,χ))
      (analyticAt_const.prod analyticAt_id)).continuousAt
  refine (denseRange_finiteSourcePairs (p := 2) (by simp)).induction_on φ ?_ ?_
  · simp only [CoeffPair.cotangentCoefficients_fst,CoeffPair.cotangentCoefficients_snd]
    exact (isClosed_le (hF.clm_apply continuous_const).norm (by fun_prop)).inter
      (isClosed_le (hF.clm_apply continuous_const).norm (by fun_prop))
  · intro a
    rw [cotangentCoefficients_sourceDiscriminant_finite_fst,
      cotangentCoefficients_sourceDiscriminant_finite_snd,
      unitFourierCoefficient_eq_interval,unitFourierCoefficient_eq_interval]
    simpa only [classicalPotentialEnergy_finiteSourceCurve,Int.cast_neg,abs_neg] using
      norm_fourier_classicalDiscriminantGradient_le_energy (finiteSourceCurve a) z (-n)

/-- One explicit inverse-bracket constant works on bounded source and
spectral balls, for both components and including zero frequency. -/
theorem norm_sourceDiscriminantCotangent_coefficient_le_of_bounds
    (φ : CoeffPair 2) (z : ℂ) (M R : ℝ) (hφ : ‖φ‖ ≤ M) (hz : ‖z‖ ≤ R) (n : ℤ) :
    ‖(CoeffPair.cotangentCoefficients (by norm_num)
      (sourceDiscriminantCotangent (by simp) z φ)).1 n‖ ≤
        (8*(Real.exp (R+1+M^2))^3*(R+2+M^2))/(1+|(n : ℝ)|) ∧
    ‖(CoeffPair.cotangentCoefficients (by norm_num)
      (sourceDiscriminantCotangent (by simp) z φ)).2 n‖ ≤
        (8*(Real.exp (R+1+M^2))^3*(R+2+M^2))/(1+|(n : ℝ)|) := by
  have hM := (norm_nonneg φ).trans hφ
  have hsq := (sq_le_sq₀ (norm_nonneg φ) hM).mpr hφ
  have hb : (8*(Real.exp (‖z‖+1+‖φ‖^2))^3*(‖z‖+2+‖φ‖^2))/(1+|(n : ℝ)|) ≤
      (8*(Real.exp (R+1+M^2))^3*(R+2+M^2))/(1+|(n : ℝ)|) := by gcongr
  obtain ⟨h₁,h₂⟩ := norm_sourceDiscriminantCotangent_coefficient_le_energy φ z n
  exact ⟨h₁.trans hb,h₂.trans hb⟩

/-- The full bounded family of actual cotangent coordinates has one
square-summable majorant, not merely separate bounds on each cotangent norm. -/
theorem exists_sourceDiscriminantCotangent_coefficient_majorant
    (M R : ℝ) (hR : 0 ≤ R) :
    ∃ b : Coeff 2, ∀ (φ : CoeffPair 2), ‖φ‖ ≤ M → ∀ z : ℂ, ‖z‖ ≤ R → ∀ n : ℤ,
      ‖(CoeffPair.cotangentCoefficients (by norm_num)
        (sourceDiscriminantCotangent (by simp) z φ)).1 n‖ ≤ ‖b n‖ ∧
      ‖(CoeffPair.cotangentCoefficients (by norm_num)
        (sourceDiscriminantCotangent (by simp) z φ)).2 n‖ ≤ ‖b n‖ := by
  let C : ℝ := 8*(Real.exp (R+1+M^2))^3*(R+2+M^2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let b : Coeff 2 := (C : ℂ) • WeightedCoeff.inverseWeight (Weight.sobolev 1)
    (Weight.inverse_sobolev_one_memlp (by norm_num : (1 : ℝ≥0∞) < 2))
  refine ⟨b,?_⟩
  intro φ hφ z hz n
  have hbn : ‖b n‖ = C/(1+|(n : ℝ)|) := by
    change ‖(C : ℂ)*(Weight.sobolev 1 n : ℂ)⁻¹‖ = _
    simp only [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hC,
      Weight.sobolev_apply,Real.rpow_one,abs_of_pos (by positivity : 0 < 1+|(n : ℝ)|),
      div_eq_mul_inv]
  rw [hbn]
  exact norm_sourceDiscriminantCotangent_coefficient_le_of_bounds φ z M R hφ hz n

/-- Both actual cotangent tails become uniformly small over simultaneous
bounded Hilbert source and spectral balls. The cutoff is chosen before the
potential and spectral parameter. -/
theorem eventually_small_sourceDiscriminantCotangent_tails
    (M R : ℝ) (hR : 0 ≤ R) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ s : Finset ℤ in atTop, ∀ (φ : CoeffPair 2), ‖φ‖ ≤ M → ∀ z : ℂ, ‖z‖ ≤ R →
      let g := CoeffPair.cotangentCoefficients (by norm_num)
        (sourceDiscriminantCotangent (by simp) z φ)
      ‖g.1-Coeff.truncate s g.1‖ < ε ∧ ‖g.2-Coeff.truncate s g.2‖ < ε := by
  obtain ⟨b,hb⟩ := exists_sourceDiscriminantCotangent_coefficient_majorant M R hR
  filter_upwards [Coeff.eventually_small_tails_of_majorant (by simp) b ε hε] with s hs φ hφ z hz
  exact ⟨hs _ (fun n => (hb φ hφ z hz n).1),hs _ (fun n => (hb φ hφ z hz n).2)⟩

end NLS.ZakharovShabat
