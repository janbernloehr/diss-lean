import NLS.ZakharovShabat.SourceBoundarySimpleDifferential
import NLS.ZakharovShabat.SourceDirichletNormalizedGradient

/-! # Actual Dirichlet gradients on a common complex source neighborhood

The canonical simple-root differential is transported to its physical
normalized squared eigenfunction. The neighborhood supplies analyticity and
simplicity at every index, so the final statements assume neither separately.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Complex MeasureTheory Filter Topology NLS.LinearVolterra NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- At included Hilbert sources, the actual characteristic derivative in
any compatible direction agrees with its physical derivative at every finite
source exponent at least two. No reality assumption is needed. -/
theorem sourceBoundaryCharacteristicCotangent_exponent_continuous_direction
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (φ h : CoeffPair 2) (Φ H : Curve (ℂ × ℂ))
    (hΦ : physicalBase (periodOnePotential φ) =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (hH : physicalBase (periodOnePotential h) =ᵐ[volume.restrict (Ioc 0 1)] extend H) (z : ℂ) :
    sourceBoundaryCharacteristicCotangent hp hp1 b z (CoeffPair.exponentInclusion h2p φ)
      (CoeffPair.exponentInclusion h2p h) =
      (fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalSeparatedCharacteristic b Ψ z) Φ) H := by
  let F : CoeffPair p → ℂ := fun ψ => periodOneBoundaryCharacteristic hp hp1 b ψ z
  have hF : DifferentiableAt ℂ F (CoeffPair.exponentInclusion h2p φ) :=
    ((analyticOnNhd_periodOneBoundaryCharacteristic_joint hp hp1 b
      (z,CoeffPair.exponentInclusion h2p φ) (mem_univ _)).comp
      (f := fun ψ : CoeffPair p => (z,ψ)) (analyticAt_const.prod analyticAt_id)).differentiableAt
  have he : (fun ψ : CoeffPair 2 => periodOneBoundaryCharacteristic (by simp) (by norm_num) b ψ z) =
      F ∘ CoeffPair.exponentInclusion h2p := by
    funext ψ
    exact congrFun (periodOneBoundaryCharacteristic_exponent (by simp) hp (by norm_num) hp1 h2p b ψ) z
  have hd := congrArg (fun f : CoeffPair 2 → ℂ => (fderiv ℂ f φ) h) he
  rw [fderiv_comp φ hF (CoeffPair.exponentInclusion h2p).differentiableAt,
    ContinuousLinearMap.fderiv,ContinuousLinearMap.comp_apply] at hd
  exact hd.symm.trans (sourceBoundaryCharacteristicCotangent_continuous_direction b φ h Φ H hΦ hH z)

/-- At an actual complex simple canonical root, nonzero normalization and
the normalized integral follow from the actual source differential. -/
theorem canonicalDirichletRoot_normalized_integral_of_simple
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ : CoeffPair 2) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase (periodOnePotential φ) =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) (n : ℤ)
    (hμ : DifferentiableAt ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n)
      (CoeffPair.exponentInclusion h2p φ))
    (hs : deriv (periodOneBoundaryCharacteristic hp hp1 .dirichlet (CoeffPair.exponentInclusion h2p φ))
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (CoeffPair.exponentInclusion h2p φ) n) ≠ 0) :
    let z := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (CoeffPair.exponentInclusion h2p φ) n
    classicalDirichletNormalization Φ z ≠ 0 ∧
      ∀ (h : CoeffPair 2) (H : Curve (ℂ × ℂ)),
        physicalBase (periodOnePotential h) =ᵐ[volume.restrict (Ioc 0 1)] extend H →
        (fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n)
          (CoeffPair.exponentInclusion h2p φ)) (CoeffPair.exponentInclusion h2p h) =
          ∫ t in (0 : ℝ)..1, (classicalDirichletNormalizedGradient Φ z t).1*(extend H t).1+
            (classicalDirichletNormalizedGradient Φ z t).2*(extend H t).2 := by
  dsimp only
  let z := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (CoeffPair.exponentInclusion h2p φ) n
  have he : periodOneBoundaryCharacteristic hp hp1 .dirichlet (CoeffPair.exponentInclusion h2p φ) =
      classicalSeparatedCharacteristic .dirichlet Φ := by
    rw [← periodOneBoundaryCharacteristic_exponent (by simp) hp (by norm_num) hp1 h2p .dirichlet φ]
    exact funext (periodOneBoundaryCharacteristic_eq_classical_of_continuous .dirichlet φ Φ hΦ)
  have hz : classicalSeparatedCharacteristic .dirichlet Φ z = 0 := by
    rw [← he]
    exact periodOneBoundaryCharacteristic_at_canonicalRoot_eq_zero hp hp1 .dirichlet _ n
  have hs' : deriv (classicalSeparatedCharacteristic .dirichlet Φ) z ≠ 0 := by
    rw [← he]
    exact hs
  refine ⟨classicalDirichletNormalization_ne_zero_of_simple Φ z hz hs',?_⟩
  intro h H hH
  rw [fderiv_canonicalPeriodOneBoundaryRoot_eq_cotangent_of_simple hp hp1 .dirichlet _ n hμ hs]
  simp only [smul_apply,smul_eq_mul]
  rw [sourceBoundaryCharacteristicCotangent_exponent_continuous_direction hp hp1 h2p .dirichlet φ h Φ H hΦ hH,
    he,fderiv_classicalSeparatedCharacteristic_eq_gradient_integral,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
  dsimp only
  rw [classicalDirichletNormalizedGradient_eq_characteristic_quotient Φ z hz hs' ⟨t,ht'⟩]
  simp only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

/-- All canonical Dirichlet root gradients on one complex neighborhood of
the whole real source locus have the genuine normalized physical integral.
Analyticity, simplicity and nonzero normalization are proved, not supplied. -/
theorem exists_global_source_dirichlet_normalized_integral
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ (φ : CoeffPair 2), CoeffPair.exponentInclusion h2p φ ∈ W →
      ∀ (Φ : Curve (ℂ × ℂ)),
        physicalBase (periodOnePotential φ) =ᵐ[volume.restrict (Ioc 0 1)] extend Φ →
      ∀ n : ℤ,
        let z := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (CoeffPair.exponentInclusion h2p φ) n
        classicalDirichletNormalization Φ z ≠ 0 ∧
          ∀ (h : CoeffPair 2) (H : Curve (ℂ × ℂ)),
            physicalBase (periodOnePotential h) =ᵐ[volume.restrict (Ioc 0 1)] extend H →
            (fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n)
              (CoeffPair.exponentInclusion h2p φ)) (CoeffPair.exponentInclusion h2p h) =
              ∫ t in (0 : ℝ)..1, (classicalDirichletNormalizedGradient Φ z t).1*(extend H t).1+
                (classicalDirichletNormalizedGradient Φ z t).2*(extend H t).2 := by
  obtain ⟨W,hW,hreal,hroots⟩ := exists_sourceBoundaryRoots_simple_common_domain hp hp1
  refine ⟨W,hW,hreal,?_⟩
  intro φ hφ Φ hΦ n
  obtain ⟨hμ,hs⟩ := hroots _ hφ .dirichlet n
  exact canonicalDirichletRoot_normalized_integral_of_simple hp hp1 h2p φ Φ hΦ n hμ.differentiableAt hs

end NLS.ZakharovShabat
