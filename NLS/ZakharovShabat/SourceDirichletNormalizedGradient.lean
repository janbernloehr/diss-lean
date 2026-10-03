import NLS.ZakharovShabat.ContinuousSourceBoundaryGradient
import NLS.ZakharovShabat.ClassicalDirichletRootGradient
import NLS.ZakharovShabat.SourceBoundaryExponentDifferential
import NLS.ZakharovShabat.SourceMidpointSobolevSummability

/-! # Normalized physical gradients of the canonical source Dirichlet roots

The source characteristic and its physical realization agree at every
compatible continuous potential. Simplicity of the canonical real-source
roots therefore supplies the nonzero bilinear normalization, at every index.
The actual source differential has the normalized squared-eigenfunction
integral, and exponent inclusion preserves its unit Fourier values.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Complex MeasureTheory Filter Topology NLS.LinearVolterra NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Canonical real-source Dirichlet roots have nonzero physical normalization;
there is no additional simplicity or integral nonvanishing premise. -/
theorem classicalDirichletNormalization_canonicalRoot_ne_zero
    (φ : CoeffPair 2) (hreal : IsRealType (CoeffPair.toMax 2 φ))
    (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase (periodOnePotential φ) =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) (n : ℤ) :
    classicalDirichletNormalization Φ (canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet φ n) ≠ 0 := by
  have he : periodOneBoundaryCharacteristic (by simp) (by norm_num) .dirichlet φ =
      classicalSeparatedCharacteristic .dirichlet Φ :=
    funext (periodOneBoundaryCharacteristic_eq_classical_of_continuous .dirichlet φ Φ hΦ)
  apply classicalDirichletNormalization_ne_zero_of_simple
  · rw [← he]
    exact periodOneBoundaryCharacteristic_at_canonicalRoot_eq_zero (by simp) (by norm_num) .dirichlet φ n
  · rw [← he]
    exact deriv_periodOneBoundaryCharacteristic_at_canonicalRoot_ne_zero_of_realType
      (by simp) (by norm_num) .dirichlet φ hreal n

/-- The actual canonical Hilbert source root derivative is its normalized
physical integral in every compatible continuous direction. -/
theorem fderiv_canonicalDirichletRoot_eq_normalized_integral
    (φ h : CoeffPair 2) (hreal : IsRealType (CoeffPair.toMax 2 φ))
    (Φ H : Curve (ℂ × ℂ))
    (hΦ : physicalBase (periodOnePotential φ) =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (hH : physicalBase (periodOnePotential h) =ᵐ[volume.restrict (Ioc 0 1)] extend H) (n : ℤ) :
    (fderiv ℂ (fun ψ : CoeffPair 2 => canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet ψ n) φ) h =
      ∫ t in (0 : ℝ)..1,
        (classicalDirichletNormalizedGradient Φ (canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet φ n) t).1*(extend H t).1+
        (classicalDirichletNormalizedGradient Φ (canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet φ n) t).2*(extend H t).2 := by
  let z := canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet φ n
  have he : periodOneBoundaryCharacteristic (by simp) (by norm_num) .dirichlet φ =
      classicalSeparatedCharacteristic .dirichlet Φ :=
    funext (periodOneBoundaryCharacteristic_eq_classical_of_continuous .dirichlet φ Φ hΦ)
  have hz : classicalSeparatedCharacteristic .dirichlet Φ z = 0 := by
    rw [← he]
    exact periodOneBoundaryCharacteristic_at_canonicalRoot_eq_zero (by simp) (by norm_num) .dirichlet φ n
  have hs : deriv (classicalSeparatedCharacteristic .dirichlet Φ) z ≠ 0 := by
    rw [← he]
    exact deriv_periodOneBoundaryCharacteristic_at_canonicalRoot_ne_zero_of_realType
      (by simp) (by norm_num) .dirichlet φ hreal n
  rw [fderiv_canonicalPeriodOneBoundaryRoot_eq_cotangent (by simp) (by norm_num) .dirichlet φ hreal n]
  simp only [smul_apply,smul_eq_mul]
  rw [sourceBoundaryCharacteristicCotangent_continuous_direction .dirichlet φ h Φ H hΦ hH,
    he,fderiv_classicalSeparatedCharacteristic_eq_gradient_integral,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
  dsimp only
  rw [classicalDirichletNormalizedGradient_eq_characteristic_quotient Φ z hz hs ⟨t,ht'⟩]
  simp only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

/-- Inclusion into any finite source exponent at least two preserves the
normalized derivative formula, with the same canonical signed root. -/
theorem fderiv_canonicalDirichletRoot_exponent_eq_normalized_integral
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ h : CoeffPair 2) (hreal : IsRealType (CoeffPair.toMax 2 φ))
    (Φ H : Curve (ℂ × ℂ))
    (hΦ : physicalBase (periodOnePotential φ) =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (hH : physicalBase (periodOnePotential h) =ᵐ[volume.restrict (Ioc 0 1)] extend H) (n : ℤ) :
    (fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n)
      (CoeffPair.exponentInclusion h2p φ)) (CoeffPair.exponentInclusion h2p h) =
      ∫ t in (0 : ℝ)..1,
        (classicalDirichletNormalizedGradient Φ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet
          (CoeffPair.exponentInclusion h2p φ) n) t).1*(extend H t).1+
        (classicalDirichletNormalizedGradient Φ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet
          (CoeffPair.exponentInclusion h2p φ) n) t).2*(extend H t).2 := by
  have he := congrArg (fun L : CoeffPair 2 →L[ℂ] ℂ => L h)
    (fderiv_canonicalPeriodOneBoundaryRoots_exponent (by simp) hp (by norm_num) hp1 h2p .dirichlet n ⟨φ,hreal⟩)
  change (fderiv ℂ (fun ψ : CoeffPair 2 => canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet ψ n) φ) h = _ at he
  simp only [ContinuousLinearMap.comp_apply] at he
  rw [← he,← canonicalPeriodOneBoundaryRoots_exponent (by simp) hp (by norm_num) hp1 h2p .dirichlet φ]
  exact fderiv_canonicalDirichletRoot_eq_normalized_integral φ h hreal Φ H hΦ hH n

/-- The first unit Fourier value of the actual source root cotangent is the
first normalized physical gradient coefficient at reversed frequency. -/
theorem fderiv_canonicalDirichletRoot_single_fst
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ : CoeffPair 2) (hreal : IsRealType (CoeffPair.toMax 2 φ))
    (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase (periodOnePotential φ) =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) (n k : ℤ) :
    (fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n)
      (CoeffPair.exponentInclusion h2p φ)) (CoeffPair.inlCLM (lp.single p k 1)) =
      unitFourierCoefficient (fun t => (classicalDirichletNormalizedGradient Φ
        (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (CoeffPair.exponentInclusion h2p φ) n) t).1) (-k) := by
  have hdir : CoeffPair.inlCLM (lp.single p k (1 : ℂ)) =
      CoeffPair.exponentInclusion h2p (CoeffPair.ofFinsupp (p := 2) (Finsupp.single k 1,0)) := by
    rw [CoeffPair.exponentInclusion_ofFinsupp]
    apply (CoeffPair.toMax p).injective
    apply Prod.ext <;> ext m <;> simp [lp.single_apply,Pi.single_apply,Finsupp.single_apply,eq_comm]
  rw [hdir,fderiv_canonicalDirichletRoot_exponent_eq_normalized_integral hp hp1 h2p φ _ hreal Φ _ hΦ
    (finiteSource_physical_compatibility (Finsupp.single k 1,0)).1]
  unfold unitFourierCoefficient
  rw [show -(2*(-k)) = 2*k by ring]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
  simp [NLS.LinearVolterra.extend,projIcc_of_mem _ ht',finiteSourceCurve,BoundaryCondition.periodOnePair,polynomial]

/-- The second unit Fourier value retains the second physical component
and the same reversed-frequency convention. -/
theorem fderiv_canonicalDirichletRoot_single_snd
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ : CoeffPair 2) (hreal : IsRealType (CoeffPair.toMax 2 φ))
    (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase (periodOnePotential φ) =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) (n k : ℤ) :
    (fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n)
      (CoeffPair.exponentInclusion h2p φ)) (CoeffPair.inrCLM (lp.single p k 1)) =
      unitFourierCoefficient (fun t => (classicalDirichletNormalizedGradient Φ
        (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (CoeffPair.exponentInclusion h2p φ) n) t).2) (-k) := by
  have hdir : CoeffPair.inrCLM (lp.single p k (1 : ℂ)) =
      CoeffPair.exponentInclusion h2p (CoeffPair.ofFinsupp (p := 2) (0,Finsupp.single k 1)) := by
    rw [CoeffPair.exponentInclusion_ofFinsupp]
    apply (CoeffPair.toMax p).injective
    apply Prod.ext <;> ext m <;> simp [lp.single_apply,Pi.single_apply,Finsupp.single_apply,eq_comm]
  rw [hdir,fderiv_canonicalDirichletRoot_exponent_eq_normalized_integral hp hp1 h2p φ _ hreal Φ _ hΦ
    (finiteSource_physical_compatibility (0,Finsupp.single k 1)).1]
  unfold unitFourierCoefficient
  rw [show -(2*(-k)) = 2*k by ring]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
  simp [NLS.LinearVolterra.extend,projIcc_of_mem _ ht',finiteSourceCurve,BoundaryCondition.periodOnePair,polynomial]

/-- At a physical H¹ source, the normalization and both actual source
cotangent coefficients are identified without a supplied physical gradient. -/
theorem canonicalDirichletRoot_sobolev_normalized_gradient
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ : CoeffPair 2) (hreal : IsRealType (CoeffPair.toMax 2 φ))
    (a : Domain 2) (ha : periodOnePotential φ = domainInclusion a) (n : ℤ) :
    let z := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (CoeffPair.exponentInclusion h2p φ) n
    let L := fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n)
      (CoeffPair.exponentInclusion h2p φ)
    classicalDirichletNormalization (classicalSobolevPotential a) z ≠ 0 ∧
      ∀ k : ℤ,
        L (CoeffPair.inlCLM (lp.single p k 1)) =
          unitFourierCoefficient (fun t => (classicalDirichletNormalizedGradient (classicalSobolevPotential a) z t).1) (-k) ∧
        L (CoeffPair.inrCLM (lp.single p k 1)) =
          unitFourierCoefficient (fun t => (classicalDirichletNormalizedGradient (classicalSobolevPotential a) z t).2) (-k) := by
  dsimp only
  have hΦ := physicalBase_source_sobolev_compatibility φ a ha
  refine ⟨?_,fun k => ⟨fderiv_canonicalDirichletRoot_single_fst hp hp1 h2p φ hreal _ hΦ n k,
    fderiv_canonicalDirichletRoot_single_snd hp hp1 h2p φ hreal _ hΦ n k⟩⟩
  rw [← canonicalPeriodOneBoundaryRoots_exponent (by simp) hp (by norm_num) hp1 h2p .dirichlet φ]
  exact classicalDirichletNormalization_canonicalRoot_ne_zero φ hreal _ hΦ n

end NLS.ZakharovShabat
