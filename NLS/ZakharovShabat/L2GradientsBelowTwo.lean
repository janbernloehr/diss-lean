import NLS.ZakharovShabat.L2CanonicalMidpointGradient
import NLS.SequenceSpaces.PairExponentIdentity

/-! # Actual physical gradients on source spaces below the Hilbert exponent

Source inclusion into exponent two preserves the spectral coordinates.
On complex neighborhoods of the real source locus, differentiating that
identity transfers the actual physical formulas to every source direction.
-/
noncomputable section
open Set Complex MeasureTheory
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The physical midpoint gradient uses the canonical Hilbert representative. -/
def sourceMidpointPhysicalGradientBelowTwo (hp2 : p ≤ 2) (φ : CoeffPair p) (n : ℤ) : ℝ → ℂ × ℂ :=
  sourceMidpointPhysicalGradient (by simp) (by norm_num) (le_rfl : (2 : ℝ≥0∞) ≤ 2)
    (CoeffPair.exponentInclusion hp2 φ) n

/-- The source midpoint derivative is the restriction of its actual Hilbert derivative. -/
theorem fderiv_midpoint_below_two_of_hilbert_differentiable
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2) (φ : CoeffPair p) (n : ℤ)
    (hd : DifferentiableAt ℂ (fun ψ : CoeffPair 2 => canonicalPeriodicMidpoint (by simp) (by norm_num)
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n) (CoeffPair.exponentInclusion hp2 φ)) :
    fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n) φ =
      (fderiv ℂ (fun ψ : CoeffPair 2 => canonicalPeriodicMidpoint (by simp) (by norm_num)
        (periodOnePotential ψ) (periodOnePotential_mem ψ) n) (CoeffPair.exponentInclusion hp2 φ)).comp
          (CoeffPair.exponentInclusion hp2) := by
  have he : (fun ψ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n) =
      (fun ψ : CoeffPair 2 => canonicalPeriodicMidpoint (by simp) (by norm_num)
        (periodOnePotential ψ) (periodOnePotential_mem ψ) n) ∘ CoeffPair.exponentInclusion hp2 := by
    funext ψ
    exact canonicalPeriodicMidpoint_source_exponent hp (by simp) hp1 (by norm_num) hp2 ψ n
  rw [he,fderiv_comp φ hd (CoeffPair.exponentInclusion hp2).differentiableAt,ContinuousLinearMap.fderiv]

/-- The same restriction identity applies to actual canonical Dirichlet roots. -/
theorem fderiv_dirichlet_below_two_of_hilbert_differentiable
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2) (φ : CoeffPair p) (n : ℤ)
    (hd : DifferentiableAt ℂ (fun ψ : CoeffPair 2 => canonicalPeriodOneBoundaryRoots (by simp) (by norm_num)
      .dirichlet ψ n) (CoeffPair.exponentInclusion hp2 φ)) :
    fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n) φ =
      (fderiv ℂ (fun ψ : CoeffPair 2 => canonicalPeriodOneBoundaryRoots (by simp) (by norm_num)
        .dirichlet ψ n) (CoeffPair.exponentInclusion hp2 φ)).comp (CoeffPair.exponentInclusion hp2) := by
  have he : (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n) =
      (fun ψ : CoeffPair 2 => canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet ψ n) ∘
        CoeffPair.exponentInclusion hp2 := by
    funext ψ
    exact congrFun (canonicalPeriodOneBoundaryRoots_exponent hp (by simp) hp1 (by norm_num) hp2 .dirichlet ψ) n
  rw [he,fderiv_comp φ hd (CoeffPair.exponentInclusion hp2).differentiableAt,ContinuousLinearMap.fderiv]

/-- On one complex source neighborhood, every midpoint differential has the
canonical physical integral in every direction of the original source space. -/
theorem exists_global_source_midpoint_below_two_integral
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧ ∀ φ ∈ W, ∀ (n : ℤ) (h : CoeffPair p),
      (fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) n) φ) h =
        ∫ s in (0 : ℝ)..1, (sourceMidpointPhysicalGradientBelowTwo hp2 φ n s).1*
          (physicalBase (periodOnePotential (CoeffPair.exponentInclusion hp2 h)) s).1+
          (sourceMidpointPhysicalGradientBelowTwo hp2 φ n s).2*
            (physicalBase (periodOnePotential (CoeffPair.exponentInclusion hp2 h)) s).2 := by
  obtain ⟨U,hU,_,hUr,hAn⟩ := exists_global_source_analytic_midpoint_squaredGap (p := 2) (by simp) (by norm_num)
  obtain ⟨V,hV,hVr,hgrad⟩ := exists_global_source_midpoint_physical_gradient
    (p := 2) (by simp) (by norm_num) le_rfl
  refine ⟨(CoeffPair.exponentInclusion hp2) ⁻¹' (U ∩ V),
    (hU.inter hV).preimage (CoeffPair.exponentInclusion hp2).continuous,?_,?_⟩
  · intro φ hφ
    have hr := (realTypeSourceExponentInclusion hp2 ⟨φ,hφ⟩).property
    exact ⟨hUr hr,hVr hr⟩
  · intro φ hφ n h
    rw [fderiv_midpoint_below_two_of_hilbert_differentiable hp hp1 hp2 φ n (hAn _ hφ.1 n).1.differentiableAt,
      ContinuousLinearMap.comp_apply]
    have hV' : CoeffPair.exponentInclusion (le_rfl : (2 : ℝ≥0∞) ≤ 2) (CoeffPair.exponentInclusion hp2 φ) ∈ V := by
      simpa only [CoeffPair.exponentInclusion_refl] using hφ.2
    have hi := (hgrad _ hV' n).1 (CoeffPair.exponentInclusion hp2 h)
    simpa only [sourceMidpointRestrictedCotangent,ContinuousLinearMap.comp_apply,CoeffPair.exponentInclusion_refl,
      sourceMidpointPhysicalGradientBelowTwo,sourceMidpointPhysicalGradient]
      using hi

/-- Simple Dirichlet roots supply nonzero normalization throughout a complex
neighborhood, with the full original-source directional integral. -/
theorem exists_global_source_dirichlet_below_two_integral
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧ ∀ φ ∈ W, ∀ n : ℤ,
      let Φ := CoeffPair.exponentInclusion hp2 φ
      let z := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n
      l2DirichletNormalization (sourcePhysicalL2 Φ) z ≠ 0 ∧ ∀ h : CoeffPair p,
        (fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n) φ) h =
          ∫ s in (0 : ℝ)..1, (l2DirichletNormalizedGradient (sourcePhysicalL2 Φ) z s).1*
            (physicalBase (periodOnePotential (CoeffPair.exponentInclusion hp2 h)) s).1+
            (l2DirichletNormalizedGradient (sourcePhysicalL2 Φ) z s).2*
              (physicalBase (periodOnePotential (CoeffPair.exponentInclusion hp2 h)) s).2 := by
  obtain ⟨U,hU,hUr,hroots⟩ := exists_sourceBoundaryRoots_simple_common_domain (p := 2) (by simp) (by norm_num)
  obtain ⟨V,hV,hVr,hgrad⟩ := exists_global_source_dirichlet_l2_normalized_integral
    (p := 2) (by simp) (by norm_num) le_rfl
  refine ⟨(CoeffPair.exponentInclusion hp2) ⁻¹' (U ∩ V),
    (hU.inter hV).preimage (CoeffPair.exponentInclusion hp2).continuous,?_,?_⟩
  · intro φ hφ
    have hr := (realTypeSourceExponentInclusion hp2 ⟨φ,hφ⟩).property
    exact ⟨hUr hr,hVr hr⟩
  · intro φ hφ n
    dsimp only
    rw [canonicalPeriodOneBoundaryRoots_exponent hp (by simp) hp1 (by norm_num) hp2 .dirichlet φ]
    have hV' : CoeffPair.exponentInclusion (le_rfl : (2 : ℝ≥0∞) ≤ 2) (CoeffPair.exponentInclusion hp2 φ) ∈ V := by
      simpa only [CoeffPair.exponentInclusion_refl] using hφ.2
    obtain ⟨hQ,hi⟩ := hgrad _ hV' n
    simp only [CoeffPair.exponentInclusion_refl] at hQ hi
    refine ⟨hQ,?_⟩
    intro h
    rw [fderiv_dirichlet_below_two_of_hilbert_differentiable hp hp1 hp2 φ n
      (hroots _ hφ.1 .dirichlet n).1.differentiableAt,ContinuousLinearMap.comp_apply]
    exact hi (CoeffPair.exponentInclusion hp2 h)

end NLS.ZakharovShabat
