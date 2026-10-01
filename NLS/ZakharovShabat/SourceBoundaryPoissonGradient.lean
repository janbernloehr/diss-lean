import NLS.ZakharovShabat.ClassicalSeparatedGradient
import NLS.ZakharovShabat.FiniteSourceDiscriminantGradient

/-! # Actual source cotangents of the separated characteristics

The exact finite-source characteristic identity compares the actual source
Frechet derivative with the constructed physical endpoint gradient. Testing
Fourier coordinate directions proves the reversed-frequency cotangent
coefficients needed for the source Poisson calculation.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Complex MeasureTheory NLS.LinearVolterra NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The actual source differential at a fixed spectral parameter. -/
def sourceBoundaryCharacteristicCotangent {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (z : ℂ) (φ : CoeffPair p) :
    CoeffPair p →L[ℂ] ℂ :=
  fderiv ℂ (fun ψ : CoeffPair p => periodOneBoundaryCharacteristic hp hp1 b ψ z) φ

/-- The exact finite realization identifies the two actual characteristic
Frechet derivatives in every finite direction. -/
theorem sourceBoundaryCharacteristicCotangent_finite_direction
    (b : BoundaryCondition) (a c : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (z : ℂ) :
    sourceBoundaryCharacteristicCotangent (by simp) (by norm_num) b z
      (CoeffPair.ofFinsupp (p := 2) a) (CoeffPair.ofFinsupp (p := 2) c) =
        (fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalSeparatedCharacteristic b Ψ z)
          (finiteSourceCurve a)) (finiteSourceCurve c) := by
  apply fderiv_finiteSource_comparison
  · exact ((analyticOnNhd_periodOneBoundaryCharacteristic_joint (by simp) (by norm_num) b
      (z,CoeffPair.ofFinsupp (p := 2) a) (mem_univ _)).comp
      (f := fun ψ : CoeffPair 2 => (z,ψ)) (analyticAt_const.prod analyticAt_id)).differentiableAt
  · exact ((analyticOnNhd_classicalSeparatedCharacteristic_joint b (z,finiteSourceCurve a)
      (mem_univ _)).comp
      (f := fun Ψ : Curve (ℂ × ℂ) => (z,Ψ)) (analyticAt_const.prod analyticAt_id)).differentiableAt
  · exact fun c => periodOneBoundaryCharacteristic_finite_eq_classical b c z

/-- The first actual source cotangent coefficient is the physical first separated
gradient coefficient at the reversed frequency. -/
theorem cotangentCoefficients_sourceBoundaryCharacteristic_finite_fst
    (b : BoundaryCondition) (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (z : ℂ) (n : ℤ) :
    (CoeffPair.cotangentCoefficients (by norm_num)
      (sourceBoundaryCharacteristicCotangent (by simp) (by norm_num) b z (CoeffPair.ofFinsupp (p := 2) a))).1 n =
        unitFourierCoefficient (fun s => (classicalSeparatedGradient b (finiteSourceCurve a) z s).1) (-n) := by
  rw [CoeffPair.cotangentCoefficients_fst]
  have hdir : CoeffPair.inlCLM (lp.single (2 : ℝ≥0∞) n (1 : ℂ)) =
      CoeffPair.ofFinsupp (p := 2) (Finsupp.single n 1,0) := by
    apply (CoeffPair.toMax 2).injective
    apply Prod.ext <;> ext m <;> simp [lp.single_apply,Pi.single_apply,Finsupp.single_apply,eq_comm]
  rw [hdir,sourceBoundaryCharacteristicCotangent_finite_direction,
    fderiv_classicalSeparatedCharacteristic_eq_gradient_integral]
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
theorem cotangentCoefficients_sourceBoundaryCharacteristic_finite_snd
    (b : BoundaryCondition) (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (z : ℂ) (n : ℤ) :
    (CoeffPair.cotangentCoefficients (by norm_num)
      (sourceBoundaryCharacteristicCotangent (by simp) (by norm_num) b z (CoeffPair.ofFinsupp (p := 2) a))).2 n =
        unitFourierCoefficient (fun s => (classicalSeparatedGradient b (finiteSourceCurve a) z s).2) (-n) := by
  rw [CoeffPair.cotangentCoefficients_snd]
  have hdir : CoeffPair.inrCLM (lp.single (2 : ℝ≥0∞) n (1 : ℂ)) =
      CoeffPair.ofFinsupp (p := 2) (0,Finsupp.single n 1) := by
    apply (CoeffPair.toMax 2).injective
    apply Prod.ext <;> ext m <;> simp [lp.single_apply,Pi.single_apply,Finsupp.single_apply,eq_comm]
  rw [hdir,sourceBoundaryCharacteristicCotangent_finite_direction,
    fderiv_classicalSeparatedCharacteristic_eq_gradient_integral]
  unfold unitFourierCoefficient
  rw [show -(2*(-n)) = 2*n by ring]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs
  simp [NLS.LinearVolterra.extend,projIcc_of_mem _ hs',finiteSourceCurve,
    BoundaryCondition.periodOnePair,polynomial]

end NLS.ZakharovShabat
