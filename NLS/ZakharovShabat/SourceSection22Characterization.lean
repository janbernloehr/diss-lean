import NLS.ZakharovShabat.SourceSection22Global
import NLS.ZakharovShabat.HigherExponentAnalyticNLSSolutions
/-! # Original phase characterization at every finite exponent

Smooth approximation and continuity force the physical coordinate law.
Conversely, a continuous curve with that law remains in the actual image,
so the original inverse flow proves the smooth-approximation condition.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceSection20Data
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W₀ W V Wa B U : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {D : SourceSection17OriginalData hp hp1 W₀ W V s}
  {A : SourceAbelianMomentAtlas hp hp1 Wa s} (Q : SourceSection20Data D A B U)
include Q

/-- Every actual smooth renormalized solution obeys the original physical phase law. -/
theorem smooth_renormalized_phase (f : SmoothNLSData) (τ : ℝ) :
    sourceComplexBirkhoffMap hp hp1 s (f.renormalizedSource p τ).val =
      Birkhoff.hamiltonianPhaseFlow (A.phaseFrequency (f.source p)) τ
        (sourceComplexBirkhoffMap hp hp1 s (f.source p).val) := by
  have he : f.renormalizedSource p τ = A.hamiltonianRenormalizedImageFlow D.complex (f.source p) τ := by
    have h := A.classicalRenormalizedNLS_source_eq_imageFlow Q.roots.toSourcePsiIsolatingComplexExtension
      D.complex f.renormalized f.renormalized_isClassical τ
    change f.renormalizedSource p τ = A.hamiltonianRenormalizedImageFlow D.complex
      (f.renormalizedSource p 0) τ at h
    simpa only [SmoothNLSData.renormalizedSource_zero] using! h
  have hvalid : (-τ,f.source p) ∈ A.renormalizedImageDomain s := by
    rcases le_total p 2 with hp2 | h2p
    · exact D.complex.proposition17_3 hp2 _
    · exact A.smoothPeriodOneSourceAt_mem_renormalizedImageDomain Q.roots.toSourcePsiIsolatingComplexExtension
        D.complex h2p f.value f.smooth f.periodic τ
  rw [he,SourceAbelianMomentAtlas.hamiltonianRenormalizedImageFlow,
    A.complex_map_renormalizedImageFlow D.complex _ _ hvalid]
  rfl

/-- Every approximation solution has the original coordinates, at every finite p > 1. -/
theorem renormalized_solution_coordinates (J : Set ℝ) (φ : realTypeSourceSubmodule p)
    (γ : ℝ → realTypeSourceSubmodule p) (hγ : IsRenormalizedNLSSolutionOn J φ γ)
    (τ : ℝ) (hτ : τ ∈ J) :
    sourceComplexBirkhoffMap hp hp1 s (γ τ).val =
      Birkhoff.hamiltonianPhaseFlow (A.phaseFrequency φ) τ
        (sourceComplexBirkhoffMap hp hp1 s φ.val) := by
  obtain ⟨f,hf⟩ := exists_smoothNLSData_sequence hp hp1 φ
  have hleft := D.complex.continuous_complex_map_real.continuousAt.tendsto.comp
    (hγ.approximation f hf τ hτ)
  have hright := Q.hamiltonian_phase_joint_continuous.continuousAt.tendsto.comp
    (tendsto_const_nhds.prodMk_nhds hf : Tendsto (fun j => (τ,(f j).source p)) atTop (𝓝 (τ,φ)))
  have he (j : ℕ) := Q.smooth_renormalized_phase (f j) τ
  simp only [Function.comp_def,he] at hleft
  exact tendsto_nhds_unique hleft hright

/-- Corrected Remark 22.3 at every finite p > 1, with the original solution definition.
The coordinate identity itself supplies the image guard needed above two. -/
theorem remark22_3 (T : ℝ) (hT : 0 ≤ T)
    (φ : realTypeSourceSubmodule p) (γ : ℝ → realTypeSourceSubmodule p) :
    IsRenormalizedNLSSolutionOn (Icc (-T) T) φ γ ↔
      ContinuousOn γ (Icc (-T) T) ∧
      ∀ τ ∈ Icc (-T) T, sourceComplexBirkhoffMap hp hp1 s (γ τ).val =
        Birkhoff.hamiltonianPhaseFlow (A.phaseFrequency φ) τ
          (sourceComplexBirkhoffMap hp hp1 s φ.val) := by
  constructor
  · intro hγ
    exact ⟨hγ.continuous,Q.renormalized_solution_coordinates _ φ γ hγ⟩
  · rintro ⟨hc,he⟩
    have h0 : (0 : ℝ) ∈ Icc (-T) T := ⟨neg_nonpos.mpr hT,hT⟩
    rcases le_total p 2 with hp2 | h2p
    · exact (Q.renormalized_solution_iff_coordinates hp2 _ φ γ).mpr ⟨h0,hc,he⟩
    have hvalid : φ ∈ A.renormalizedTrajectoryDomain s T := by
      intro τ
      have he' := he (-τ.val) (by constructor <;> linarith [τ.property.1,τ.property.2])
      change sourceComplexBirkhoffMap hp hp1 s (γ (-τ.val)).val =
        Birkhoff.phaseFlow (A.phaseFrequency φ) (-(-τ.val))
          (sourceComplexBirkhoffMap hp hp1 s φ.val) at he'
      rw [neg_neg] at he'
      change Birkhoff.decodeReal (Birkhoff.phaseFlow (A.phaseFrequency φ) τ.val
        (sourceComplexBirkhoffMap hp hp1 s φ.val)) ∈ range (sourceRealBirkhoffMap hp hp1 s)
      rw [← he',← D.complex.encode_real_map,Birkhoff.decodeReal_encodeReal]
      exact mem_range_self _
    have hgood := A.renormalizedImageFlow_isSolution Q.roots D.roots_open D.roots_real_subset
      D.complex h2p φ T hT hvalid
    have hsame : EqOn γ (A.hamiltonianRenormalizedImageFlow D.complex φ) (Icc (-T) T) := by
      intro τ hτ
      apply D.complex.complex_map_real_injective
      change sourceComplexBirkhoffMap hp hp1 s (γ τ).val =
        sourceComplexBirkhoffMap hp hp1 s
          (A.hamiltonianRenormalizedImageFlow D.complex φ τ).val
      rw [he τ hτ,SourceAbelianMomentAtlas.hamiltonianRenormalizedImageFlow,
        A.complex_map_renormalizedImageFlow D.complex φ (-τ)
          (hvalid (hamiltonianTimeReflection T ⟨τ,hτ⟩))]
      rfl
    refine ⟨h0,hc,?_,?_⟩
    · rw [hsame h0,A.hamiltonianRenormalizedImageFlow_zero]
    · intro f hf τ hτ
      rw [hsame hτ]
      exact hgood.approximation f hf τ hτ

/-- The image condition is exactly when the total inverse formula defines a physical
solution on the asserted interval; no fallback value outside the image is used. -/
theorem trajectory_domain_iff_solution (T : ℝ) (hT : 0 ≤ T) (φ : realTypeSourceSubmodule p) :
    φ ∈ A.renormalizedTrajectoryDomain s T ↔
      IsRenormalizedNLSSolutionOn (Icc (-T) T) φ
        (A.hamiltonianRenormalizedImageFlow D.complex φ) := by
  constructor
  · intro hvalid
    rcases le_total p 2 with hp2 | h2p
    · have he : A.hamiltonianRenormalizedImageFlow D.complex φ =
          A.hamiltonianRenormalizedSourceFlow D.complex hp2 φ :=
        funext (A.hamiltonianRenormalizedImageFlow_eq_global D.complex hp2 φ)
      rw [he]
      exact (Q.global_physical_solutions hp2 φ).1.restrict (subset_univ _)
        ⟨neg_nonpos.mpr hT,hT⟩
    · exact A.renormalizedImageFlow_isSolution Q.roots D.roots_open D.roots_real_subset
        D.complex h2p φ T hT hvalid
  · intro hsol τ
    have he := Q.renormalized_solution_coordinates _ φ _ hsol (-τ.val)
      (show -τ.val ∈ Icc (-T) T by constructor <;> linarith [τ.property.1,τ.property.2])
    change sourceComplexBirkhoffMap hp hp1 s
      (A.hamiltonianRenormalizedImageFlow D.complex φ (-τ.val)).val =
        Birkhoff.phaseFlow (A.phaseFrequency φ) (-(-τ.val))
          (sourceComplexBirkhoffMap hp hp1 s φ.val) at he
    rw [neg_neg] at he
    change Birkhoff.decodeReal (Birkhoff.phaseFlow (A.phaseFrequency φ) τ.val
      (sourceComplexBirkhoffMap hp hp1 s φ.val)) ∈ range (sourceRealBirkhoffMap hp hp1 s)
    rw [← he,← D.complex.encode_real_map,Birkhoff.decodeReal_encodeReal]
    exact mem_range_self _

/-- The corrected coordinate law gives uniqueness in the full continuous-curve class,
without a restriction-space or extra differentiability assumption. -/
theorem coordinate_curve_unique (T : ℝ) (hT : 0 ≤ T) (φ : realTypeSourceSubmodule p)
    (γ η : ℝ → realTypeSourceSubmodule p)
    (hγ : ContinuousOn γ (Icc (-T) T)) (hη : ContinuousOn η (Icc (-T) T))
    (heγ : ∀ τ ∈ Icc (-T) T, sourceComplexBirkhoffMap hp hp1 s (γ τ).val =
      Birkhoff.hamiltonianPhaseFlow (A.phaseFrequency φ) τ (sourceComplexBirkhoffMap hp hp1 s φ.val))
    (heη : ∀ τ ∈ Icc (-T) T, sourceComplexBirkhoffMap hp hp1 s (η τ).val =
      Birkhoff.hamiltonianPhaseFlow (A.phaseFrequency φ) τ (sourceComplexBirkhoffMap hp hp1 s φ.val)) :
    EqOn γ η (Icc (-T) T) := by
  have hγ' := (Q.remark22_3 T hT φ γ).mpr ⟨hγ,heγ⟩
  have hη' := (Q.remark22_3 T hT φ η).mpr ⟨hη,heη⟩
  simpa only [inter_self] using hγ'.eqOn_inter hη' hp hp1

end NLS.ZakharovShabat.SourceSection20Data
