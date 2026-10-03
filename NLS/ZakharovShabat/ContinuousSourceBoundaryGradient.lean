import NLS.ZakharovShabat.ContinuousSourceBoundaryRealization

/-! # Actual boundary characteristic cotangents at continuous source potentials

Affine physical compatibility identifies the genuine source derivative with
the physical endpoint derivative. Unit Fourier directions recover its two
coefficients with the source's reversed-frequency convention.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Complex MeasureTheory NLS.LinearVolterra NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Differentiating the exact source/classical identity along a compatible
continuous direction compares the two actual Fréchet derivatives. -/
theorem sourceBoundaryCharacteristicCotangent_continuous_direction
    (b : BoundaryCondition) (φ h : CoeffPair 2) (Φ H : Curve (ℂ × ℂ))
    (hΦ : physicalBase (periodOnePotential φ) =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (hH : physicalBase (periodOnePotential h) =ᵐ[volume.restrict (Ioc 0 1)] extend H) (z : ℂ) :
    sourceBoundaryCharacteristicCotangent (by simp) (by norm_num) b z φ h =
      (fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalSeparatedCharacteristic b Ψ z) Φ) H := by
  let F : CoeffPair 2 → ℂ := fun ψ => periodOneBoundaryCharacteristic (by simp) (by norm_num) b ψ z
  let G : Curve (ℂ × ℂ) → ℂ := fun Ψ => classicalSeparatedCharacteristic b Ψ z
  have hF : DifferentiableAt ℂ F φ :=
    ((analyticOnNhd_periodOneBoundaryCharacteristic_joint (by simp) (by norm_num) b
      (z,φ) (mem_univ _)).comp (f := fun ψ : CoeffPair 2 => (z,ψ))
        (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hG : DifferentiableAt ℂ G Φ :=
    ((analyticOnNhd_classicalSeparatedCharacteristic_joint b (z,Φ) (mem_univ _)).comp
      (f := fun Ψ : Curve (ℂ × ℂ) => (z,Ψ)) (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hφline : HasDerivAt (fun c : ℂ => φ+c • h) h 0 := by
    simpa only [one_smul] using! ((hasDerivAt_id (0 : ℂ)).smul_const h).const_add φ
  have hΦline : HasDerivAt (fun c : ℂ => Φ+c • H) H 0 := by
    simpa only [one_smul] using! ((hasDerivAt_id (0 : ℂ)).smul_const H).const_add Φ
  have h₁ : HasDerivAt (F ∘ fun c : ℂ => φ+c • h) ((fderiv ℂ F φ) h) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq (𝕜 := ℂ) (E := ℂ) (F := CoeffPair 2)
      (0 : ℂ) hF.hasFDerivAt hφline (by simp)
  have h₂ : HasDerivAt (G ∘ fun c : ℂ => Φ+c • H) ((fderiv ℂ G Φ) H) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq (𝕜 := ℂ) (E := ℂ) (F := Curve (ℂ × ℂ))
      (0 : ℂ) hG.hasFDerivAt hΦline (by ext t <;> simp)
  have heq : (F ∘ fun c : ℂ => φ+c • h) = (G ∘ fun c : ℂ => Φ+c • H) := by
    funext c
    exact periodOneBoundaryCharacteristic_eq_classical_of_continuous b _ _
      (physicalBase_source_affine_compatibility φ h Φ H hΦ hH c) z
  rw [heq] at h₁
  exact h₁.unique h₂

/-- Every finite source direction can be tested at an arbitrary continuously
represented potential, without finite support at the base point. -/
theorem sourceBoundaryCharacteristicCotangent_finite_direction_of_continuous
    (b : BoundaryCondition) (φ : CoeffPair 2) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase (periodOnePotential φ) =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (z : ℂ) :
    sourceBoundaryCharacteristicCotangent (by simp) (by norm_num) b z φ (CoeffPair.ofFinsupp (p := 2) a) =
      (fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalSeparatedCharacteristic b Ψ z) Φ) (finiteSourceCurve a) :=
  sourceBoundaryCharacteristicCotangent_continuous_direction b φ _ Φ _ hΦ (finiteSource_physical_compatibility a).1 z

/-- The first physical gradient coefficient gives the actual source
cotangent coefficient at reversed frequency for every continuous representative. -/
theorem cotangentCoefficients_sourceBoundaryCharacteristic_continuous_fst
    (b : BoundaryCondition) (φ : CoeffPair 2) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase (periodOnePotential φ) =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) (z : ℂ) (n : ℤ) :
    (CoeffPair.cotangentCoefficients (by norm_num)
      (sourceBoundaryCharacteristicCotangent (by simp) (by norm_num) b z φ)).1 n =
        unitFourierCoefficient (fun t => (classicalSeparatedGradient b Φ z t).1) (-n) := by
  rw [CoeffPair.cotangentCoefficients_fst]
  have hdir : CoeffPair.inlCLM (lp.single (2 : ℝ≥0∞) n (1 : ℂ)) =
      CoeffPair.ofFinsupp (p := 2) (Finsupp.single n 1,0) := by
    apply (CoeffPair.toMax 2).injective
    apply Prod.ext <;> ext m <;> simp [lp.single_apply,Pi.single_apply,Finsupp.single_apply,eq_comm]
  rw [hdir,sourceBoundaryCharacteristicCotangent_finite_direction_of_continuous b φ Φ hΦ,
    fderiv_classicalSeparatedCharacteristic_eq_gradient_integral]
  unfold unitFourierCoefficient
  rw [show -(2*(-n)) = 2*n by ring]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
  simp [NLS.LinearVolterra.extend,projIcc_of_mem _ ht',finiteSourceCurve,
    BoundaryCondition.periodOnePair,polynomial]

/-- The second physical coefficient has the same reversed frequency and
retains the second component's original gradient sign. -/
theorem cotangentCoefficients_sourceBoundaryCharacteristic_continuous_snd
    (b : BoundaryCondition) (φ : CoeffPair 2) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase (periodOnePotential φ) =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) (z : ℂ) (n : ℤ) :
    (CoeffPair.cotangentCoefficients (by norm_num)
      (sourceBoundaryCharacteristicCotangent (by simp) (by norm_num) b z φ)).2 n =
        unitFourierCoefficient (fun t => (classicalSeparatedGradient b Φ z t).2) (-n) := by
  rw [CoeffPair.cotangentCoefficients_snd]
  have hdir : CoeffPair.inrCLM (lp.single (2 : ℝ≥0∞) n (1 : ℂ)) =
      CoeffPair.ofFinsupp (p := 2) (0,Finsupp.single n 1) := by
    apply (CoeffPair.toMax 2).injective
    apply Prod.ext <;> ext m <;> simp [lp.single_apply,Pi.single_apply,Finsupp.single_apply,eq_comm]
  rw [hdir,sourceBoundaryCharacteristicCotangent_finite_direction_of_continuous b φ Φ hΦ,
    fderiv_classicalSeparatedCharacteristic_eq_gradient_integral]
  unfold unitFourierCoefficient
  rw [show -(2*(-n)) = 2*n by ring]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
  simp [NLS.LinearVolterra.extend,projIcc_of_mem _ ht',finiteSourceCurve,
    BoundaryCondition.periodOnePair,polynomial]

end NLS.ZakharovShabat
