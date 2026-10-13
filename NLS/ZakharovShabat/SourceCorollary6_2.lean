import NLS.ZakharovShabat.SourcePeriodTwoRestriction
import NLS.ZakharovShabat.SourceBoundaryOverview
import NLS.ZakharovShabat.SourceBoundaryRootSpaces
import NLS.ZakharovShabat.SourceAuxiliaryPotentialPhase
import NLS.ZakharovShabat.SourceAuxiliaryRootSpaces
import NLS.ZakharovShabat.SourceAuxiliaryReality

/-!
# Corollary 6.2 for arbitrary original period-two inputs

Restriction to [0,1] is performed before the ordinary Dirichlet or auxiliary
Neumann reflection. Thus all four complete canonical root sequences belong
to the actual original restricted spectra, with full Jordan multiplicities.
Their complete displacement power sums are bounded on one original-input
neighborhood, including all central labels.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The complete ordinary boundary roots of an arbitrary period-two input. -/
def sourcePeriodTwoBoundaryRoots (hp1 : 1 < p) (hp : p ≠ ⊤) (b : BoundaryCondition)
    (φ : CoeffPair p) : ℤ → ℂ :=
  canonicalPeriodOneBoundaryRoots hp hp1 b (sourcePeriodTwoRestriction hp1 hp φ)

/-- The complete auxiliary boundary roots of an arbitrary period-two input. -/
def sourcePeriodTwoAuxiliaryRoots (hp1 : 1 < p) (hp : p ≠ ⊤) (b : BoundaryCondition)
    (φ : CoeffPair p) : ℤ → ℂ :=
  canonicalAuxiliaryPeriodOneRoots hp hp1 b (sourcePeriodTwoRestriction hp1 hp φ)

/-- The ordinary labels exhaust the actual original-norm spectrum after restriction and reflection. -/
theorem sourcePeriodTwoBoundaryRoots_exhaustive (hp1 : 1 < p) (hp : p ≠ ⊤)
    (b : BoundaryCondition) (φ : CoeffPair p) (z : ℂ) :
    z ∈ sourceBoundarySpectrum b hp (sourceReflectedPotential hp1 hp (sourcePeriodTwoRestriction hp1 hp φ))
      (sourceReflectedPotential_mem hp1 hp (sourcePeriodTwoRestriction hp1 hp φ)) ↔
      ∃ n : ℤ, sourcePeriodTwoBoundaryRoots hp1 hp b φ n = z :=
  mem_sourceBoundarySpectrum_reflected_iff b hp1 hp _ z

/-- The auxiliary labels exhaust the actual original-norm auxiliary spectrum. -/
theorem sourcePeriodTwoAuxiliaryRoots_exhaustive (hp1 : 1 < p) (hp : p ≠ ⊤)
    (b : BoundaryCondition) (φ : CoeffPair p) (z : ℂ) :
    z ∈ sourceAuxiliarySpectrum b hp
      (sourceAuxiliaryReflectedPotential hp1 hp (sourcePeriodTwoRestriction hp1 hp φ))
      (sourceAuxiliaryReflectedPotential_mem hp1 hp (sourcePeriodTwoRestriction hp1 hp φ)) ↔
      ∃ n : ℤ, sourcePeriodTwoAuxiliaryRoots hp1 hp b φ n = z := by
  rw [sourceAuxiliarySpectrum_eq_sourcePhaseBoundary, sourceAuxiliaryPotentialPhase_eq_sourcePhase]
  simp only [sourcePeriodTwoAuxiliaryRoots, canonicalAuxiliaryPeriodOneRoots_eq_sourcePhase]
  exact canonicalPeriodOneBoundaryRoots_exhaustive hp hp1 b _ z

/-- Ordinary root repetitions count the full original Jordan multiplicity. -/
theorem sourcePeriodTwoBoundaryRoots_multiplicity (hp1 : 1 < p) (hp : p ≠ ⊤)
    (b : BoundaryCondition) (φ : CoeffPair p) (z : ℂ) :
    (∑ᶠ n : ℤ, if sourcePeriodTwoBoundaryRoots hp1 hp b φ n = z then (1 : ℕ) else 0) =
      sourceBoundaryAlgebraicMultiplicity b hp
        (sourceReflectedPotential hp1 hp (sourcePeriodTwoRestriction hp1 hp φ))
        (sourceReflectedPotential_mem hp1 hp (sourcePeriodTwoRestriction hp1 hp φ)) z := by
  rw [sourceBoundaryAlgebraicMultiplicity_eq]
  trans b.algebraicMultiplicity hp (periodOneBoundaryPotential hp hp1 (sourcePeriodTwoRestriction hp1 hp φ)).val
    (periodOneBoundaryPotential hp hp1 (sourcePeriodTwoRestriction hp1 hp φ)).property z
  · exact canonicalPeriodOneBoundaryRoots_multiplicity hp hp1 b _ z
  · congr 1
    exact (toMax_sourceReflectedPotential hp1 hp _).symm

/-- Auxiliary root repetitions count the full original auxiliary Jordan multiplicity. -/
theorem sourcePeriodTwoAuxiliaryRoots_multiplicity (hp1 : 1 < p) (hp : p ≠ ⊤)
    (b : BoundaryCondition) (φ : CoeffPair p) (z : ℂ) :
    (∑ᶠ n : ℤ, if sourcePeriodTwoAuxiliaryRoots hp1 hp b φ n = z then (1 : ℕ) else 0) =
      sourceAuxiliaryAlgebraicMultiplicity b hp
        (sourceAuxiliaryReflectedPotential hp1 hp (sourcePeriodTwoRestriction hp1 hp φ))
        (sourceAuxiliaryReflectedPotential_mem hp1 hp (sourcePeriodTwoRestriction hp1 hp φ)) z := by
  rw [sourceAuxiliaryAlgebraicMultiplicity_eq]
  trans b.auxiliaryAlgebraicMultiplicity hp (auxiliaryPeriodOnePotential hp hp1 (sourcePeriodTwoRestriction hp1 hp φ)).val
    (auxiliaryPeriodOnePotential hp hp1 (sourcePeriodTwoRestriction hp1 hp φ)).property z
  · exact canonicalAuxiliaryPeriodOneRoots_multiplicity hp hp1 b _ z
  · congr 1
    exact (toMax_sourceAuxiliaryReflectedPotential hp1 hp _).symm

private theorem sourceBoundaryPowerPullback (hp1 : 1 < p) (hp : p ≠ ⊤)
    (F : CoeffPair p →L[ℂ] CoeffPair p) (φ : CoeffPair p) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∃ C : ℝ, 0 < C ∧ ∀ ψ ∈ U, ∀ b : BoundaryCondition,
        Summable (fun n : ℤ => ‖canonicalPeriodOneBoundaryRoots hp hp1 b (F ψ) n-(Real.pi : ℂ)*n‖^p.toReal) ∧
        (∑' n : ℤ, ‖canonicalPeriodOneBoundaryRoots hp hp1 b (F ψ) n-(Real.pi : ℂ)*n‖^p.toReal) ≤ C := by
  obtain ⟨V,ho,hc,hφ,h0,C,hC,hb⟩ := sourceTheorem1_5 hp hp1 (F φ)
  exact ⟨F ⁻¹' V,ho.preimage F.continuous,hc.linear_preimage (F.restrictScalars ℝ).toLinearMap,
    hφ,by simpa only [Set.mem_preimage,map_zero] using h0,C,hC,fun ψ hψ b => hb (F ψ) hψ b⟩

/-- Corollary 6.2: all four complete root sequences have locally uniformly
bounded displacement power sums on the original period-two source space. -/
theorem sourceCorollary6_2 (hp1 : 1 < p) (hp : p ≠ ⊤) (φ : CoeffPair p) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∃ C : ℝ, 0 < C ∧ ∀ ψ ∈ U, ∀ b : BoundaryCondition,
        (Summable (fun n : ℤ => ‖sourcePeriodTwoBoundaryRoots hp1 hp b ψ n-(Real.pi : ℂ)*n‖^p.toReal) ∧
          (∑' n : ℤ, ‖sourcePeriodTwoBoundaryRoots hp1 hp b ψ n-(Real.pi : ℂ)*n‖^p.toReal) ≤ C) ∧
        (Summable (fun n : ℤ => ‖sourcePeriodTwoAuxiliaryRoots hp1 hp b ψ n-(Real.pi : ℂ)*n‖^p.toReal) ∧
          (∑' n : ℤ, ‖sourcePeriodTwoAuxiliaryRoots hp1 hp b ψ n-(Real.pi : ℂ)*n‖^p.toReal) ≤ C) := by
  let F := sourcePeriodTwoRestriction hp1 hp
  let G := (sourcePhase (p := p)).comp F
  obtain ⟨U,ho,hc,hφ,h0,C,hC,hb⟩ := sourceBoundaryPowerPullback hp1 hp F φ
  obtain ⟨V,hVo,hVc,hVφ,hV0,D,hD,hd⟩ := sourceBoundaryPowerPullback hp1 hp G φ
  refine ⟨U ∩ V,ho.inter hVo,hc.inter hVc,⟨hφ,hVφ⟩,⟨h0,hV0⟩,
    max C D,hC.trans_le (le_max_left _ _),?_⟩
  intro ψ hψ b
  have hl := hb ψ hψ.1 b
  have hr := hd ψ hψ.2 b
  refine ⟨⟨hl.1,hl.2.trans (le_max_left _ _)⟩,?_⟩
  simp only [sourcePeriodTwoAuxiliaryRoots, canonicalAuxiliaryPeriodOneRoots_eq_sourcePhase]
  exact ⟨hr.1,hr.2.trans (le_max_right _ _)⟩

/-- All four actual displacement sequences belong to ℓᵖ, including central indices. -/
theorem sourceCorollary6_2_mem (hp1 : 1 < p) (hp : p ≠ ⊤) (b : BoundaryCondition) (φ : CoeffPair p) :
    Memℓp (fun n : ℤ => sourcePeriodTwoBoundaryRoots hp1 hp b φ n-(Real.pi : ℂ)*n) p ∧
      Memℓp (fun n : ℤ => sourcePeriodTwoAuxiliaryRoots hp1 hp b φ n-(Real.pi : ℂ)*n) p := by
  obtain ⟨U,_,_,hφ,_,C,_,hb⟩ := sourceCorollary6_2 hp1 hp φ
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp
  exact ⟨(memℓp_gen_iff hp0).mpr (hb φ hφ b).1.1,(memℓp_gen_iff hp0).mpr (hb φ hφ b).2.1⟩

end NLS.ZakharovShabat
