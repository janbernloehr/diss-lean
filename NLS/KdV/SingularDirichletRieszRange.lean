import NLS.KdV.SingularDirichletRieszProjection
import NLS.KdV.SingularDirichletAlgebraicMultiplicity
import NLS.FunctionalAnalysis.IdempotentRootSpaces
import NLS.FunctionalAnalysis.FiniteInvariantSpectrum

/-! The ACTUAL native complex Dirichlet Riesz range is exactly the sum of
ALL enclosed FULL algebraic root spaces, including associated vectors. -/
noncomputable section
open Set Metric
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue
local instance dirichletRieszRangeH1NormedGroup : NormedAddCommGroup UnitDirichletH1 := unitDirichletSubspace.normedAddCommGroup
local instance dirichletRieszRangeH1NormedSpace : NormedSpace ℂ UnitDirichletH1 := unitDirichletSubspace.normedSpace
local instance dirichletRieszRangeBaseNormedGroup : NormedAddCommGroup UnitDirichletHminus := inferInstance
local instance dirichletRieszRangeBaseNormedSpace : NormedSpace ℂ UnitDirichletHminus := inferInstance

/-- The actual compact base inverse is injective on its ENTIRE native dual. -/
theorem singularDirichletBaseResolvent_injective
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (a : ℂ)
    (ha : a ∈ singularDirichletResolventSet q) :
    Function.Injective (singularDirichletBaseResolvent q a) := by
  change Function.Injective (singularDirichletBaseResolvent q a).toLinearMap
  rw [← pencilResolvent_singularDirichletPencilEquiv q a ha]
  exact NLS.FunctionalAnalysis.pencilResolvent_injective _
    singularDirichletDomainInclusion_injective _

/-- First native root vectors are exactly original full-domain eigenvectors. -/
theorem mem_singularDirichletRootSpace_one
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ) (x : UnitDirichletHminus) :
    x ∈ singularDirichletRootSpace q z 1 ↔ ∃ f : UnitDirichletH1,
      singularDirichletDomainInclusion f = x ∧
      singularDirichletOperator q f = z • singularDirichletDomainInclusion f := by
  rw [mem_singularDirichletRootSpace_succ q z 0 x]
  change (∃ f : UnitDirichletH1, singularDirichletDomainInclusion f = x ∧
    singularDirichletPencil q z f = 0) ↔ _
  simp only [singularDirichletPencil_eq_zero_iff]

/-- The actual finite spectral range is invariant under every full-base resolvent. -/
theorem singularDirichletRieszProjection_range_invariant
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : sphere c r ⊆ singularDirichletResolventSet q) (a : ℂ)
    (ha : a ∈ singularDirichletResolventSet q) :
    MapsTo (singularDirichletBaseResolvent q a)
      (singularDirichletRieszProjection q c r).range
      (singularDirichletRieszProjection q c r).range := by
  rintro x ⟨y,rfl⟩
  refine ⟨singularDirichletBaseResolvent q a y,?_⟩
  exact congrArg (fun T : UnitDirichletHminus →L[ℂ] UnitDirichletHminus => T y)
    (commute_singularDirichletRieszProjection_resolvent q c r hr hc a ha).eq

/-- The actual projection fixes every full physical root vector inside its circle,
including generalized vectors for complex potentials. -/
theorem singularDirichletRieszProjection_root_inside (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hc : sphere c ρ ⊆ singularDirichletResolventSet q) (a : ℂ)
    (ha : a ∈ singularDirichletResolventSet q) (z : ℂ) (hz : z ∈ ball c ρ)
    (x : UnitDirichletHminus)
    (hx : x ∈ singularDirichletRootSpaceTop q z) :
    singularDirichletRieszProjection q c ρ x = x := by
  by_cases hza : z = a
  · subst z
    rw [singularDirichletRootSpaceTop_eq_bot_of_mem_resolvent q a ha] at hx
    have hx0 : x = 0 := hx
    rw [hx0, map_zero]
  let P := singularDirichletRieszProjection q c ρ
  let T : Module.End ℂ (UnitDirichletHminus) :=
    (singularDirichletBaseResolvent q a).toLinearMap
  have hP : IsIdempotentElem P.toLinearMap := congrArg ContinuousLinearMap.toLinearMap
    (isIdempotentElem_singularDirichletRieszProjection q c ρ hρ hc)
  have hPT : Commute P.toLinearMap T := congrArg ContinuousLinearMap.toLinearMap
    (commute_singularDirichletRieszProjection_resolvent q c ρ hρ.le hc a ha).eq
  apply NLS.FunctionalAnalysis.idempotent_eq_self_on_genEigenspace_top
    P.toLinearMap T hP hPT (z-a)⁻¹ _ x
      (by rwa [singularDirichletRootSpaceTop_eq_resolvent q a z ha hza] at hx)
  intro y hy
  have hm : y ∈ singularDirichletRootSpace q z 1 := by
    rw [singularDirichletRootSpace_eq_resolvent q a z ha hza]
    exact Module.End.mem_genEigenspace_one.mpr hy
  obtain ⟨f, hfy, hf⟩ := (mem_singularDirichletRootSpace_one _ z y).mp hm
  change singularDirichletRieszProjection q c ρ y = y
  rw [← hfy]
  exact singularDirichletRieszProjection_eigenvector_inside q c ρ hρ hc z hz f hf

/-- Outside the closed disk the actual projection kills the entire physical
algebraic root space, without a reality or semisimplicity hypothesis. -/
theorem singularDirichletRieszProjection_root_outside (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hc : sphere c ρ ⊆ singularDirichletResolventSet q) (a : ℂ)
    (ha : a ∈ singularDirichletResolventSet q) (z : ℂ) (hz : z ∉ closedBall c ρ)
    (x : UnitDirichletHminus)
    (hx : x ∈ singularDirichletRootSpaceTop q z) :
    singularDirichletRieszProjection q c ρ x = 0 := by
  by_cases hza : z = a
  · subst z
    rw [singularDirichletRootSpaceTop_eq_bot_of_mem_resolvent q a ha] at hx
    have hx0 : x = 0 := hx
    rw [hx0, map_zero]
  let P := singularDirichletRieszProjection q c ρ
  let T : Module.End ℂ (UnitDirichletHminus) :=
    (singularDirichletBaseResolvent q a).toLinearMap
  have hP : IsIdempotentElem P.toLinearMap := congrArg ContinuousLinearMap.toLinearMap
    (isIdempotentElem_singularDirichletRieszProjection q c ρ hρ hc)
  have hPT : Commute P.toLinearMap T := congrArg ContinuousLinearMap.toLinearMap
    (commute_singularDirichletRieszProjection_resolvent q c ρ hρ.le hc a ha).eq
  apply NLS.FunctionalAnalysis.idempotent_eq_zero_on_genEigenspace_top
    P.toLinearMap T hP hPT (z-a)⁻¹ _ x
      (by rwa [singularDirichletRootSpaceTop_eq_resolvent q a z ha hza] at hx)
  intro y hy
  have hm : y ∈ singularDirichletRootSpace q z 1 := by
    rw [singularDirichletRootSpace_eq_resolvent q a z ha hza]
    exact Module.End.mem_genEigenspace_one.mpr hy
  obtain ⟨f, hfy, hf⟩ := (mem_singularDirichletRootSpace_one _ z y).mp hm
  change singularDirichletRieszProjection q c ρ y = 0
  rw [← hfy]
  exact singularDirichletRieszProjection_eigenvector_outside q c ρ hρ hc z hz f hf

/-- For every complex original potential, the actual Riesz range is precisely
the sum of all enclosed full physical algebraic root spaces. -/
theorem singularDirichletRieszProjection_range_eq_roots (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hc : sphere c ρ ⊆ singularDirichletResolventSet q) (a : ℂ)
    (ha : a ∈ singularDirichletResolventSet q) :
    (singularDirichletRieszProjection q c ρ).range =
      ⨆ z : ball c ρ, singularDirichletRootSpaceTop
        q z.val := by
  let P := singularDirichletRieszProjection q c ρ
  let K : Module.End ℂ (UnitDirichletHminus) :=
    (singularDirichletBaseResolvent q a).toLinearMap
  let W := P.range
  let := finiteDimensional_singularDirichletRieszProjection_range q c ρ hρ hc
  have hP := isIdempotentElem_singularDirichletRieszProjection q c ρ hρ hc
  have hfix (x : UnitDirichletHminus) (hx : x ∈ W) : P x = x := by
    obtain ⟨y, rfl⟩ := hx
    exact congrArg (fun T : UnitDirichletHminus →L[ℂ] UnitDirichletHminus => T y) hP
  have hW : ∀ x ∈ W, K x ∈ W :=
    singularDirichletRieszProjection_range_invariant q c ρ hρ.le hc a ha
  apply le_antisymm
  · change W ≤ _
    rw [NLS.FunctionalAnalysis.eq_iSup_inf_genEigenspace_of_finite K W hW]
    apply iSup_le
    intro μ
    by_cases hμ : μ = 0
    · subst μ
      rw [NLS.FunctionalAnalysis.genEigenspace_zero_eq_bot_of_injective K
        (singularDirichletBaseResolvent_injective q a ha), inf_bot_eq]
      exact bot_le
    · let z := a+μ⁻¹
      have hza : z ≠ a := by dsimp [z]; simpa using inv_ne_zero hμ
      have he : (z-a)⁻¹ = μ := by simp [z]
      have hroot : K.genEigenspace μ ⊤ =
          singularDirichletRootSpaceTop q z := by
        rw [singularDirichletRootSpaceTop_eq_resolvent q a z ha hza, he]
      intro x hx
      have hxroot := hroot ▸ hx.2
      by_cases hz : z ∈ ball c ρ
      · exact (le_iSup (fun z : ball c ρ => singularDirichletRootSpaceTop
          q z.val) ⟨z, hz⟩) hxroot
      have hx0 : x = 0 := by
        by_cases hzclosed : z ∈ closedBall c ρ
        · have hzsphere : z ∈ sphere c ρ := mem_sphere.mpr
            (le_antisymm (mem_closedBall.mp hzclosed) (not_lt.mp hz))
          rw [singularDirichletRootSpaceTop_eq_bot_of_mem_resolvent q z (hc hzsphere)] at hxroot
          exact hxroot
        · exact (hfix x hx.1).symm.trans
            (singularDirichletRieszProjection_root_outside q c ρ hρ hc a ha z hzclosed x hxroot)
      exact hx0 ▸ Submodule.zero_mem _
  · apply iSup_le
    intro z x hx
    exact ⟨x, singularDirichletRieszProjection_root_inside q c ρ hρ hc a ha z.val z.property x hx⟩

end NLS.KdV
