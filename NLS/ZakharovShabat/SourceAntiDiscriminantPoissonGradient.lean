import NLS.ZakharovShabat.ClassicalAntiDiscriminantGradient
import NLS.ZakharovShabat.FiniteSourceDiscriminantGradient

/-! # Actual source cotangent of the anti-discriminant

The exact finite-source anti-discriminant identity compares the actual source
Frechet derivative with the constructed physical off-diagonal gradient. Testing
Fourier coordinate directions proves the reversed-frequency cotangent
coefficients needed for the source Poisson calculation.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Complex MeasureTheory NLS.LinearVolterra NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The actual source differential at a fixed spectral parameter. -/
def sourceAntiDiscriminantCotangent {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (z : ℂ) (φ : CoeffPair p) :
    CoeffPair p →L[ℂ] ℂ :=
  fderiv ℂ (fun ψ : CoeffPair p => sourceAntiDiscriminantCandidate hp hp1 ψ z) φ

/-- The exact finite realization identifies the two actual anti-discriminant
Frechet derivatives in every finite direction. -/
theorem sourceAntiDiscriminantCotangent_finite_direction
    (a c : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (z : ℂ) :
    sourceAntiDiscriminantCotangent (by simp) (by norm_num) z
      (CoeffPair.ofFinsupp (p := 2) a) (CoeffPair.ofFinsupp (p := 2) c) =
        (fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalAntiDiscriminant Ψ z)
          (finiteSourceCurve a)) (finiteSourceCurve c) := by
  apply fderiv_finiteSource_comparison
  · exact ((analyticOnNhd_sourceAntiDiscriminantCandidate_joint (by simp) (by norm_num)
      (z,CoeffPair.ofFinsupp (p := 2) a) (mem_univ _)).comp
      (f := fun ψ : CoeffPair 2 => (z,ψ)) (analyticAt_const.prod analyticAt_id)).differentiableAt
  · exact ((analyticOnNhd_classicalAntiDiscriminant_joint (z,finiteSourceCurve a)
      (mem_univ _)).comp
      (f := fun Ψ : Curve (ℂ × ℂ) => (z,Ψ)) (analyticAt_const.prod analyticAt_id)).differentiableAt
  · exact fun c => sourceAntiDiscriminantCandidate_finite_eq_classical c z

/-- The first actual source cotangent coefficient is the physical first anti-discriminant
gradient coefficient at the reversed frequency. -/
theorem cotangentCoefficients_sourceAntiDiscriminant_finite_fst
    (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (z : ℂ) (n : ℤ) :
    (CoeffPair.cotangentCoefficients (by norm_num)
      (sourceAntiDiscriminantCotangent (by simp) (by norm_num) z (CoeffPair.ofFinsupp (p := 2) a))).1 n =
        unitFourierCoefficient (fun s => (classicalAntiDiscriminantGradient (finiteSourceCurve a) z s).1) (-n) := by
  rw [CoeffPair.cotangentCoefficients_fst]
  have hdir : CoeffPair.inlCLM (lp.single (2 : ℝ≥0∞) n (1 : ℂ)) =
      CoeffPair.ofFinsupp (p := 2) (Finsupp.single n 1,0) := by
    apply (CoeffPair.toMax 2).injective
    apply Prod.ext <;> ext m <;> simp [lp.single_apply,Pi.single_apply,Finsupp.single_apply,eq_comm]
  rw [hdir,sourceAntiDiscriminantCotangent_finite_direction,
    fderiv_classicalAntiDiscriminant_eq_gradient_integral]
  unfold unitFourierCoefficient
  rw [show -(2*(-n)) = 2*n by ring]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs
  simp [NLS.LinearVolterra.extend,projIcc_of_mem _ hs',finiteSourceCurve,
    BoundaryCondition.periodOnePair,polynomial]

/-- The second actual source cotangent coefficient has the same reversed
frequency, and the original second-component gradient sign. -/
theorem cotangentCoefficients_sourceAntiDiscriminant_finite_snd
    (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (z : ℂ) (n : ℤ) :
    (CoeffPair.cotangentCoefficients (by norm_num)
      (sourceAntiDiscriminantCotangent (by simp) (by norm_num) z (CoeffPair.ofFinsupp (p := 2) a))).2 n =
        unitFourierCoefficient (fun s => (classicalAntiDiscriminantGradient (finiteSourceCurve a) z s).2) (-n) := by
  rw [CoeffPair.cotangentCoefficients_snd]
  have hdir : CoeffPair.inrCLM (lp.single (2 : ℝ≥0∞) n (1 : ℂ)) =
      CoeffPair.ofFinsupp (p := 2) (0,Finsupp.single n 1) := by
    apply (CoeffPair.toMax 2).injective
    apply Prod.ext <;> ext m <;> simp [lp.single_apply,Pi.single_apply,Finsupp.single_apply,eq_comm]
  rw [hdir,sourceAntiDiscriminantCotangent_finite_direction,
    fderiv_classicalAntiDiscriminant_eq_gradient_integral]
  unfold unitFourierCoefficient
  rw [show -(2*(-n)) = 2*n by ring]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs
  simp [NLS.LinearVolterra.extend,projIcc_of_mem _ hs',finiteSourceCurve,
    BoundaryCondition.periodOnePair,polynomial]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The full actual anti-discriminant cotangent is jointly analytic as
a continuous-linear-map-valued function of parameter and source. -/
theorem analyticOnNhd_sourceAntiDiscriminantCotangent_joint
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    AnalyticOnNhd ℂ (fun t : ℂ × CoeffPair p => sourceAntiDiscriminantCotangent hp hp1 t.1 t.2) univ := by
  let F : ℂ × CoeffPair p → ℂ := fun t => sourceAntiDiscriminantCandidate hp hp1 t.2 t.1
  have hF : AnalyticOnNhd ℂ F univ := analyticOnNhd_sourceAntiDiscriminantCandidate_joint hp hp1
  have hG := NLS.ComplexAnalysis.analyticOnNhd_parameterDerivative F hF
  have heq : (fun t : ℂ × CoeffPair p => sourceAntiDiscriminantCotangent hp hp1 t.1 t.2) =
      (fun t => (fderiv ℂ F t).comp (ContinuousLinearMap.inr ℂ ℂ (CoeffPair p))) := by
    funext t
    exact NLS.ComplexAnalysis.fderiv_source_section_eq_joint F t.1 t.2 ((hF t (mem_univ _)).differentiableAt)
  rw [heq]
  exact hG

end NLS.ZakharovShabat
