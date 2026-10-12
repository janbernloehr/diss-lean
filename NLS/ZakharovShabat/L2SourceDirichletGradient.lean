import NLS.ZakharovShabat.L2DirichletRootGradient
import NLS.ZakharovShabat.L2SourceCharacteristicGradients
import NLS.ZakharovShabat.SourceBoundarySimpleDifferential

/-! # Normalized Dirichlet gradients on original Hilbert sources

Every Hilbert source and direction has a physical L2 realization. On one
common complex neighborhood of the real source locus, the actual canonical
root differential is the normalized eigenfunction integral at every index.
No continuous representative or Sobolev assumption is needed.
-/
noncomputable section
open Set Complex MeasureTheory
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Exponent inclusion preserves the physical characteristic differential. -/
theorem sourceBoundaryCharacteristicCotangent_exponent_l2_integral
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (φ h : CoeffPair 2) (z : ℂ) :
    sourceBoundaryCharacteristicCotangent hp hp1 b z (CoeffPair.exponentInclusion h2p φ)
      (CoeffPair.exponentInclusion h2p h) =
      ∫ s in (0 : ℝ)..1, (l2SeparatedGradient b (sourcePhysicalL2 φ) z s).1*
        (physicalBase (periodOnePotential h) s).1+
        (l2SeparatedGradient b (sourcePhysicalL2 φ) z s).2*(physicalBase (periodOnePotential h) s).2 := by
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
  exact hd.symm.trans (sourceBoundaryCharacteristicCotangent_eq_physical_gradient_integral b φ h z)

/-- At a simple differentiable canonical root, both normalization and the
actual integral formula hold for arbitrary Hilbert bases and directions. -/
theorem canonicalDirichletRoot_l2_normalized_integral_of_simple
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ : CoeffPair 2) (n : ℤ)
    (hμ : DifferentiableAt ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n)
      (CoeffPair.exponentInclusion h2p φ))
    (hs : deriv (periodOneBoundaryCharacteristic hp hp1 .dirichlet (CoeffPair.exponentInclusion h2p φ))
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (CoeffPair.exponentInclusion h2p φ) n) ≠ 0) :
    let z := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (CoeffPair.exponentInclusion h2p φ) n
    l2DirichletNormalization (sourcePhysicalL2 φ) z ≠ 0 ∧ ∀ h : CoeffPair 2,
      (fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n)
        (CoeffPair.exponentInclusion h2p φ)) (CoeffPair.exponentInclusion h2p h) =
        ∫ s in (0 : ℝ)..1, (l2DirichletNormalizedGradient (sourcePhysicalL2 φ) z s).1*
          (physicalBase (periodOnePotential h) s).1+
          (l2DirichletNormalizedGradient (sourcePhysicalL2 φ) z s).2*(physicalBase (periodOnePotential h) s).2 := by
  dsimp only
  let z := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (CoeffPair.exponentInclusion h2p φ) n
  have he : periodOneBoundaryCharacteristic hp hp1 .dirichlet (CoeffPair.exponentInclusion h2p φ) =
      l2SeparatedCharacteristic .dirichlet (sourcePhysicalL2 φ) := by
    rw [← periodOneBoundaryCharacteristic_exponent (by simp) hp (by norm_num) hp1 h2p .dirichlet φ]
    exact funext (periodOneBoundaryCharacteristic_eq_l2 .dirichlet φ)
  have hz : l2SeparatedCharacteristic .dirichlet (sourcePhysicalL2 φ) z = 0 := by
    rw [← he]
    exact periodOneBoundaryCharacteristic_at_canonicalRoot_eq_zero hp hp1 .dirichlet _ n
  have hs' : deriv (l2SeparatedCharacteristic .dirichlet (sourcePhysicalL2 φ)) z ≠ 0 := by
    rw [← he]
    exact hs
  refine ⟨l2DirichletNormalization_ne_zero_of_simple _ z hz hs',?_⟩
  intro h
  rw [fderiv_canonicalPeriodOneBoundaryRoot_eq_cotangent_of_simple hp hp1 .dirichlet _ n hμ hs]
  simp only [smul_apply,smul_eq_mul]
  rw [sourceBoundaryCharacteristicCotangent_exponent_l2_integral hp hp1 h2p .dirichlet φ h,
    he,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [l2DirichletNormalizedGradient_eq_characteristic_quotient _ z hz hs' s]
  simp only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

/-- One common complex domain supplies simplicity and the normalized physical
integral for every signed root and every included Hilbert source direction. -/
theorem exists_global_source_dirichlet_l2_normalized_integral
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ φ : CoeffPair 2, CoeffPair.exponentInclusion h2p φ ∈ W → ∀ n : ℤ,
        let z := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (CoeffPair.exponentInclusion h2p φ) n
        l2DirichletNormalization (sourcePhysicalL2 φ) z ≠ 0 ∧ ∀ h : CoeffPair 2,
          (fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n)
            (CoeffPair.exponentInclusion h2p φ)) (CoeffPair.exponentInclusion h2p h) =
            ∫ s in (0 : ℝ)..1, (l2DirichletNormalizedGradient (sourcePhysicalL2 φ) z s).1*
              (physicalBase (periodOnePotential h) s).1+
              (l2DirichletNormalizedGradient (sourcePhysicalL2 φ) z s).2*(physicalBase (periodOnePotential h) s).2 := by
  obtain ⟨W,hW,hreal,hroots⟩ := exists_sourceBoundaryRoots_simple_common_domain hp hp1
  refine ⟨W,hW,hreal,?_⟩
  intro φ hφ n
  obtain ⟨hμ,hs⟩ := hroots _ hφ .dirichlet n
  exact canonicalDirichletRoot_l2_normalized_integral_of_simple hp hp1 h2p φ n hμ.differentiableAt hs

end NLS.ZakharovShabat
