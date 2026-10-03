import NLS.ZakharovShabat.FiniteSourceDiscriminantGradient
import NLS.ZakharovShabat.PhysicalPotentialExtension
import NLS.ZakharovShabat.SourceDiscriminantRegularPoisson

/-! # Actual source gradients at continuous physical representatives

The physical comparison is valid at every source with a compatible
continuous representative. Only the testing directions need finite
Fourier support to recover the individual gradient coefficients.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Complex MeasureTheory NLS.LinearVolterra NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Physical compatibility is preserved along complex affine source lines. -/
theorem physicalBase_source_affine_compatibility
    (φ h : CoeffPair 2) (Φ H : Curve (ℂ × ℂ))
    (hΦ : physicalBase (periodOnePotential φ) =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (hH : physicalBase (periodOnePotential h) =ᵐ[volume.restrict (Ioc 0 1)] extend H) (c : ℂ) :
    physicalBase (periodOnePotential (φ+c • h)) =ᵐ[volume.restrict (Ioc 0 1)] extend (Φ+c • H) := by
  have hadd := ae_restrict_of_ae_restrict_of_subset
    (Ioc_subset_Ioc_right (by norm_num : (1 : ℝ) ≤ 2))
    (physicalBase_add (periodOnePotential φ) (c • periodOnePotential h))
  have hsmul := ae_restrict_of_ae_restrict_of_subset
    (Ioc_subset_Ioc_right (by norm_num : (1 : ℝ) ≤ 2))
    (physicalBase_smul c (periodOnePotential h))
  simp only [map_add,map_smul]
  filter_upwards [hadd,hsmul,hΦ,hH] with t ha hs hφ hh
  rw [ha,hs,hφ,hh]
  rfl

/-- Differentiating the exact source/classical identity along a compatible
continuous direction compares the two actual Fréchet derivatives. -/
theorem sourceDiscriminantCotangent_continuous_direction
    (φ h : CoeffPair 2) (Φ H : Curve (ℂ × ℂ))
    (hΦ : physicalBase (periodOnePotential φ) =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (hH : physicalBase (periodOnePotential h) =ᵐ[volume.restrict (Ioc 0 1)] extend H) (z : ℂ) :
    sourceDiscriminantCotangent (by simp) z φ h =
      (fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalDiscriminant Ψ z) Φ) H := by
  let F : CoeffPair 2 → ℂ := fun ψ => canonicalDiscriminant (by simp) (periodOnePotential ψ) z
  let G : Curve (ℂ × ℂ) → ℂ := fun Ψ => classicalDiscriminant Ψ z
  have hF : DifferentiableAt ℂ F φ :=
    ((analyticOnNhd_canonicalDiscriminant_periodOne (by simp) (by norm_num)
      (z,φ) (mem_univ _)).comp (f := fun ψ : CoeffPair 2 => (z,ψ))
        (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hG : DifferentiableAt ℂ G Φ :=
    ((analyticOnNhd_classicalDiscriminant_joint (z,Φ) (mem_univ _)).comp
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
    exact canonicalDiscriminant_eq_classical _ (periodOnePotential_mem _) _
      (physicalBase_source_affine_compatibility φ h Φ H hΦ hH c) z
  rw [heq] at h₁
  exact h₁.unique h₂

/-- Every finite source direction can be tested at an arbitrary continuously
represented potential, without finite support at the base point. -/
theorem sourceDiscriminantCotangent_finite_direction_of_continuous
    (φ : CoeffPair 2) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase (periodOnePotential φ) =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (b : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (z : ℂ) :
    sourceDiscriminantCotangent (by simp) z φ (CoeffPair.ofFinsupp (p := 2) b) =
      (fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalDiscriminant Ψ z) Φ) (finiteSourceCurve b) :=
  sourceDiscriminantCotangent_continuous_direction φ _ Φ _ hΦ (finiteSource_physical_compatibility b).1 z

/-- The first physical gradient coefficient gives the actual source
cotangent coefficient at reversed frequency for every continuous representative. -/
theorem cotangentCoefficients_sourceDiscriminant_continuous_fst
    (φ : CoeffPair 2) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase (periodOnePotential φ) =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) (z : ℂ) (n : ℤ) :
    (CoeffPair.cotangentCoefficients (by norm_num)
      (sourceDiscriminantCotangent (by simp) z φ)).1 n =
        unitFourierCoefficient (fun t => (classicalDiscriminantGradient Φ z t).1) (-n) := by
  rw [CoeffPair.cotangentCoefficients_fst]
  have hdir : CoeffPair.inlCLM (lp.single (2 : ℝ≥0∞) n (1 : ℂ)) =
      CoeffPair.ofFinsupp (p := 2) (Finsupp.single n 1,0) := by
    apply (CoeffPair.toMax 2).injective
    apply Prod.ext <;> ext m <;> simp [lp.single_apply,Pi.single_apply,Finsupp.single_apply,eq_comm]
  rw [hdir,sourceDiscriminantCotangent_finite_direction_of_continuous φ Φ hΦ,
    fderiv_classicalDiscriminant_eq_gradient_integral]
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
theorem cotangentCoefficients_sourceDiscriminant_continuous_snd
    (φ : CoeffPair 2) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase (periodOnePotential φ) =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) (z : ℂ) (n : ℤ) :
    (CoeffPair.cotangentCoefficients (by norm_num)
      (sourceDiscriminantCotangent (by simp) z φ)).2 n =
        unitFourierCoefficient (fun t => (classicalDiscriminantGradient Φ z t).2) (-n) := by
  rw [CoeffPair.cotangentCoefficients_snd]
  have hdir : CoeffPair.inrCLM (lp.single (2 : ℝ≥0∞) n (1 : ℂ)) =
      CoeffPair.ofFinsupp (p := 2) (0,Finsupp.single n 1) := by
    apply (CoeffPair.toMax 2).injective
    apply Prod.ext <;> ext m <;> simp [lp.single_apply,Pi.single_apply,Finsupp.single_apply,eq_comm]
  rw [hdir,sourceDiscriminantCotangent_finite_direction_of_continuous φ Φ hΦ,
    fderiv_classicalDiscriminant_eq_gradient_integral]
  unfold unitFourierCoefficient
  rw [show -(2*(-n)) = 2*n by ring]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
  simp [NLS.LinearVolterra.extend,projIcc_of_mem _ ht',finiteSourceCurve,
    BoundaryCondition.periodOnePair,polynomial]

/-- At every finite exponent at least two, the first unit source direction
still has the same physical gradient coefficient. -/
theorem sourceDiscriminantCotangent_continuous_single_fst
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ : CoeffPair 2) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase (periodOnePotential φ) =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) (z : ℂ) (n : ℤ) :
    sourceDiscriminantCotangent hp z (CoeffPair.exponentInclusion h2p φ)
      (CoeffPair.inlCLM (lp.single p n 1)) =
      unitFourierCoefficient (fun t => (classicalDiscriminantGradient Φ z t).1) (-n) := by
  have he := sourceDiscriminantRegularCotangent_coefficients_exponent (by simp) hp hp1 h2p φ z
  have hc := congrArg (fun a : Coeff 2 × Coeff 2 => a.1 n) he
  rw [(sourceDiscriminantRegularCotangent hp z (CoeffPair.exponentInclusion h2p φ)).fst_eq,
    sourceDiscriminantRegularCotangent_toCotangent] at hc
  rw [← hc]
  simpa only [sourceDiscriminantRegularCotangent,dif_pos (le_refl (2 : ℝ≥0∞)),
    NLS.Poisson.RegularSourceCotangent.ofCotangent] using
    cotangentCoefficients_sourceDiscriminant_continuous_fst φ Φ hΦ z n

/-- The second component also survives exponent inclusion without a sign change. -/
theorem sourceDiscriminantCotangent_continuous_single_snd
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ : CoeffPair 2) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase (periodOnePotential φ) =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) (z : ℂ) (n : ℤ) :
    sourceDiscriminantCotangent hp z (CoeffPair.exponentInclusion h2p φ)
      (CoeffPair.inrCLM (lp.single p n 1)) =
      unitFourierCoefficient (fun t => (classicalDiscriminantGradient Φ z t).2) (-n) := by
  have he := sourceDiscriminantRegularCotangent_coefficients_exponent (by simp) hp hp1 h2p φ z
  have hc := congrArg (fun a : Coeff 2 × Coeff 2 => a.2 n) he
  rw [(sourceDiscriminantRegularCotangent hp z (CoeffPair.exponentInclusion h2p φ)).snd_eq,
    sourceDiscriminantRegularCotangent_toCotangent] at hc
  rw [← hc]
  simpa only [sourceDiscriminantRegularCotangent,dif_pos (le_refl (2 : ℝ≥0∞)),
    NLS.Poisson.RegularSourceCotangent.ofCotangent] using
    cotangentCoefficients_sourceDiscriminant_continuous_snd φ Φ hΦ z n

end NLS.ZakharovShabat
