import NLS.ZakharovShabat.ContinuousSourceBoundaryRealization
import NLS.ZakharovShabat.SourceAntiDiscriminantPoissonGradient

/-! # Continuous physical realization of the source anti-discriminant

The phase rotation identifies the actual auxiliary characteristics with
classical monodromy at every continuously represented Hilbert source.
Differentiating this identity gives the actual anti-discriminant cotangent,
including its reversed-frequency Fourier coefficients.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Complex MeasureTheory NLS.LinearVolterra NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Opposite component phases commute with physical synthesis almost everywhere. -/
theorem physicalBase_auxiliaryPotential (φ : PairSpace 2) :
    physicalBase (auxiliaryPotential φ) =ᵐ[volume.restrict (Ioc 0 2)]
      physicalAuxiliaryPotential (physicalBase φ) := by
  have h₁ := physicalBase_smul I φ
  have h₂ := physicalBase_smul (-I) φ
  filter_upwards [h₁,h₂] with t ht₁ ht₂
  have hx := congrArg (fun v : ℂ × ℂ => v.1) ht₁
  have hy := congrArg (fun v : ℂ × ℂ => v.2) ht₂
  exact Prod.ext hx hy

/-- A compatible continuous representative retains its opposite component phases. -/
theorem physicalBase_sourcePhase_compatibility (φ : CoeffPair 2) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase (periodOnePotential φ) =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) :
    physicalBase (periodOnePotential (sourcePhase φ)) =ᵐ[volume.restrict (Ioc 0 1)]
      extend (classicalSourcePhase Φ) := by
  rw [periodOnePotential_sourcePhase]
  have hrot := ae_restrict_of_ae_restrict_of_subset
    (Ioc_subset_Ioc_right (by norm_num : (1 : ℝ) ≤ 2))
    (physicalBase_auxiliaryPotential (periodOnePotential φ))
  filter_upwards [hrot,hΦ] with t ht hΦt
  rw [ht]
  change (I * (physicalBase (periodOnePotential φ) t).1,
    -I * (physicalBase (periodOnePotential φ) t).2) = _
  rw [hΦt]
  rfl

/-- The completed starred characteristic has its exact classical normalization. -/
theorem auxiliaryPeriodOneCharacteristic_eq_classical_of_continuous
    (b : BoundaryCondition) (φ : CoeffPair 2) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase (periodOnePotential φ) =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) (z : ℂ) :
    auxiliaryPeriodOneCharacteristic (by simp) (by norm_num) b φ z =
      classicalAuxiliaryCharacteristic b Φ z := by
  rw [auxiliaryPeriodOneCharacteristic_eq_sourcePhase,
    periodOneBoundaryCharacteristic_eq_classical_of_continuous b _ _
      (physicalBase_sourcePhase_compatibility φ Φ hΦ),
    classicalAuxiliaryCharacteristic_eq_separated_phase]

/-- The actual source anti-discriminant equals the physical monodromy anti-trace. -/
theorem sourceAntiDiscriminantCandidate_eq_classical_of_continuous
    (φ : CoeffPair 2) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase (periodOnePotential φ) =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) (z : ℂ) :
    sourceAntiDiscriminantCandidate (by simp) (by norm_num) φ z =
      classicalAntiDiscriminant Φ z := by
  rw [sourceAntiDiscriminantCandidate,
    auxiliaryPeriodOneCharacteristic_eq_classical_of_continuous .neumann φ Φ hΦ,
    auxiliaryPeriodOneCharacteristic_eq_classical_of_continuous .dirichlet φ Φ hΦ,
    classicalAntiDiscriminant_eq_auxiliary_sub]

/-- Differentiating the exact source/classical identity along a compatible
continuous direction compares the two actual Fréchet derivatives. -/
theorem sourceAntiDiscriminantCotangent_continuous_direction
    (φ h : CoeffPair 2) (Φ H : Curve (ℂ × ℂ))
    (hΦ : physicalBase (periodOnePotential φ) =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (hH : physicalBase (periodOnePotential h) =ᵐ[volume.restrict (Ioc 0 1)] extend H) (z : ℂ) :
    sourceAntiDiscriminantCotangent (by simp) (by norm_num) z φ h =
      (fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalAntiDiscriminant Ψ z) Φ) H := by
  let F : CoeffPair 2 → ℂ := fun ψ => sourceAntiDiscriminantCandidate (by simp) (by norm_num) ψ z
  let G : Curve (ℂ × ℂ) → ℂ := fun Ψ => classicalAntiDiscriminant Ψ z
  have hF : DifferentiableAt ℂ F φ :=
    ((analyticOnNhd_sourceAntiDiscriminantCandidate_joint (by simp) (by norm_num)
      (z,φ) (mem_univ _)).comp (f := fun ψ : CoeffPair 2 => (z,ψ))
        (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hG : DifferentiableAt ℂ G Φ :=
    ((analyticOnNhd_classicalAntiDiscriminant_joint (z,Φ) (mem_univ _)).comp
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
    exact sourceAntiDiscriminantCandidate_eq_classical_of_continuous _ _
      (physicalBase_source_affine_compatibility φ h Φ H hΦ hH c) z
  rw [heq] at h₁
  exact h₁.unique h₂

/-- Every finite source direction can be tested at an arbitrary continuously
represented potential, without finite support at the base point. -/
theorem sourceAntiDiscriminantCotangent_finite_direction_of_continuous
    (φ : CoeffPair 2) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase (periodOnePotential φ) =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (z : ℂ) :
    sourceAntiDiscriminantCotangent (by simp) (by norm_num) z φ (CoeffPair.ofFinsupp (p := 2) a) =
      (fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalAntiDiscriminant Ψ z) Φ) (finiteSourceCurve a) :=
  sourceAntiDiscriminantCotangent_continuous_direction φ _ Φ _ hΦ (finiteSource_physical_compatibility a).1 z

/-- The first physical gradient coefficient gives the actual source
cotangent coefficient at reversed frequency for every continuous representative. -/
theorem cotangentCoefficients_sourceAntiDiscriminant_continuous_fst
    (φ : CoeffPair 2) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase (periodOnePotential φ) =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) (z : ℂ) (n : ℤ) :
    (CoeffPair.cotangentCoefficients (by norm_num)
      (sourceAntiDiscriminantCotangent (by simp) (by norm_num) z φ)).1 n =
        unitFourierCoefficient (fun t => (classicalAntiDiscriminantGradient Φ z t).1) (-n) := by
  rw [CoeffPair.cotangentCoefficients_fst]
  have hdir : CoeffPair.inlCLM (lp.single (2 : ℝ≥0∞) n (1 : ℂ)) =
      CoeffPair.ofFinsupp (p := 2) (Finsupp.single n 1,0) := by
    apply (CoeffPair.toMax 2).injective
    apply Prod.ext <;> ext m <;> simp [lp.single_apply,Pi.single_apply,Finsupp.single_apply,eq_comm]
  rw [hdir,sourceAntiDiscriminantCotangent_finite_direction_of_continuous φ Φ hΦ,
    fderiv_classicalAntiDiscriminant_eq_gradient_integral]
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
theorem cotangentCoefficients_sourceAntiDiscriminant_continuous_snd
    (φ : CoeffPair 2) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase (periodOnePotential φ) =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) (z : ℂ) (n : ℤ) :
    (CoeffPair.cotangentCoefficients (by norm_num)
      (sourceAntiDiscriminantCotangent (by simp) (by norm_num) z φ)).2 n =
        unitFourierCoefficient (fun t => (classicalAntiDiscriminantGradient Φ z t).2) (-n) := by
  rw [CoeffPair.cotangentCoefficients_snd]
  have hdir : CoeffPair.inrCLM (lp.single (2 : ℝ≥0∞) n (1 : ℂ)) =
      CoeffPair.ofFinsupp (p := 2) (0,Finsupp.single n 1) := by
    apply (CoeffPair.toMax 2).injective
    apply Prod.ext <;> ext m <;> simp [lp.single_apply,Pi.single_apply,Finsupp.single_apply,eq_comm]
  rw [hdir,sourceAntiDiscriminantCotangent_finite_direction_of_continuous φ Φ hΦ,
    fderiv_classicalAntiDiscriminant_eq_gradient_integral]
  unfold unitFourierCoefficient
  rw [show -(2*(-n)) = 2*n by ring]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
  simp [NLS.LinearVolterra.extend,projIcc_of_mem _ ht',finiteSourceCurve,
    BoundaryCondition.periodOnePair,polynomial]

/-- Restriction along coefficient inclusion preserves the complete cotangent,
for any two finite source exponents strictly above one. -/
theorem sourceAntiDiscriminantCotangent_exponent
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (φ : CoeffPair p) (z : ℂ) :
    sourceAntiDiscriminantCotangent hp hp1 z φ =
      (sourceAntiDiscriminantCotangent hq hq1 z (CoeffPair.exponentInclusion hpq φ)).comp
        (CoeffPair.exponentInclusion hpq) := by
  have heq : (fun ψ : CoeffPair p => sourceAntiDiscriminantCandidate hp hp1 ψ z) =
      (fun ψ : CoeffPair q => sourceAntiDiscriminantCandidate hq hq1 ψ z) ∘
        CoeffPair.exponentInclusion hpq := by
    funext ψ
    exact congrFun (sourceAntiDiscriminantCandidate_exponent hp hq hp1 hq1 hpq ψ) z
  have hd := ((analyticOnNhd_sourceAntiDiscriminantCandidate_joint hq hq1
    (z,CoeffPair.exponentInclusion hpq φ) (mem_univ _)).comp
    (f := fun ψ : CoeffPair q => (z,ψ)) (analyticAt_const.prod analyticAt_id)).differentiableAt
  change DifferentiableAt ℂ (fun ψ : CoeffPair q => sourceAntiDiscriminantCandidate hq hq1 ψ z) _ at hd
  unfold sourceAntiDiscriminantCotangent
  rw [heq,fderiv_comp φ hd (CoeffPair.exponentInclusion hpq).differentiableAt,
    ContinuousLinearMap.fderiv]

/-- The continuous physical anti-trace identity also holds after exponent inclusion. -/
theorem sourceAntiDiscriminantCandidate_eq_classical_of_continuous_exponent
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ : CoeffPair 2) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase (periodOnePotential φ) =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) (z : ℂ) :
    sourceAntiDiscriminantCandidate hp hp1 (CoeffPair.exponentInclusion h2p φ) z =
      classicalAntiDiscriminant Φ z := by
  rw [← sourceAntiDiscriminantCandidate_exponent (by simp) hp (by norm_num) hp1 h2p φ]
  exact sourceAntiDiscriminantCandidate_eq_classical_of_continuous φ Φ hΦ z

/-- Spectral differentiation preserves the normalization at every parameter. -/
theorem deriv_sourceAntiDiscriminantCandidate_eq_classical_of_continuous
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ : CoeffPair 2) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase (periodOnePotential φ) =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) (z : ℂ) :
    deriv (sourceAntiDiscriminantCandidate hp hp1 (CoeffPair.exponentInclusion h2p φ)) z =
      deriv (classicalAntiDiscriminant Φ) z := by
  have heq := funext (sourceAntiDiscriminantCandidate_eq_classical_of_continuous_exponent
    hp hp1 h2p φ Φ hΦ)
  rw [heq]

/-- Every compatible continuous direction is preserved after exponent inclusion. -/
theorem sourceAntiDiscriminantCotangent_continuous_direction_exponent
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ h : CoeffPair 2) (Φ H : Curve (ℂ × ℂ))
    (hΦ : physicalBase (periodOnePotential φ) =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (hH : physicalBase (periodOnePotential h) =ᵐ[volume.restrict (Ioc 0 1)] extend H) (z : ℂ) :
    sourceAntiDiscriminantCotangent hp hp1 z (CoeffPair.exponentInclusion h2p φ)
      (CoeffPair.exponentInclusion h2p h) =
      (fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalAntiDiscriminant Ψ z) Φ) H := by
  rw [← ContinuousLinearMap.comp_apply,
    ← sourceAntiDiscriminantCotangent_exponent (by simp) hp (by norm_num) hp1 h2p]
  exact sourceAntiDiscriminantCotangent_continuous_direction φ h Φ H hΦ hH z

/-- The first unit source direction gives the reversed physical Fourier coefficient
at every finite source exponent at least two. -/
theorem sourceAntiDiscriminantCotangent_continuous_single_fst
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ : CoeffPair 2) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase (periodOnePotential φ) =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) (z : ℂ) (n : ℤ) :
    sourceAntiDiscriminantCotangent hp hp1 z (CoeffPair.exponentInclusion h2p φ)
      (CoeffPair.inlCLM (lp.single p n 1)) =
      unitFourierCoefficient (fun t => (classicalAntiDiscriminantGradient Φ z t).1) (-n) := by
  have he := congrArg (fun L : CoeffPair 2 →L[ℂ] ℂ => L (CoeffPair.inlCLM (lp.single 2 n 1)))
    (sourceAntiDiscriminantCotangent_exponent (by simp) hp (by norm_num) hp1 h2p φ z)
  have hi : CoeffPair.exponentInclusion h2p (CoeffPair.inlCLM (lp.single 2 n 1)) =
      CoeffPair.inlCLM (lp.single p n 1) := by
    apply (CoeffPair.toMax p).injective
    apply Prod.ext <;> ext k <;> rfl
  simp only [ContinuousLinearMap.comp_apply,hi] at he
  rw [← he]
  simpa only [CoeffPair.cotangentCoefficients_fst] using
    cotangentCoefficients_sourceAntiDiscriminant_continuous_fst φ Φ hΦ z n

/-- The second component retains its original anti-discriminant sign. -/
theorem sourceAntiDiscriminantCotangent_continuous_single_snd
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ : CoeffPair 2) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase (periodOnePotential φ) =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) (z : ℂ) (n : ℤ) :
    sourceAntiDiscriminantCotangent hp hp1 z (CoeffPair.exponentInclusion h2p φ)
      (CoeffPair.inrCLM (lp.single p n 1)) =
      unitFourierCoefficient (fun t => (classicalAntiDiscriminantGradient Φ z t).2) (-n) := by
  have he := congrArg (fun L : CoeffPair 2 →L[ℂ] ℂ => L (CoeffPair.inrCLM (lp.single 2 n 1)))
    (sourceAntiDiscriminantCotangent_exponent (by simp) hp (by norm_num) hp1 h2p φ z)
  have hi : CoeffPair.exponentInclusion h2p (CoeffPair.inrCLM (lp.single 2 n 1)) =
      CoeffPair.inrCLM (lp.single p n 1) := by
    apply (CoeffPair.toMax p).injective
    apply Prod.ext <;> ext k <;> rfl
  simp only [ContinuousLinearMap.comp_apply,hi] at he
  rw [← he]
  simpa only [CoeffPair.cotangentCoefficients_snd] using
    cotangentCoefficients_sourceAntiDiscriminant_continuous_snd φ Φ hΦ z n

end NLS.ZakharovShabat
