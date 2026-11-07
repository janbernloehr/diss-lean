import NLS.KdV.SingularHillSpectralProjection
import NLS.FunctionalAnalysis.IdempotentRootSpaces

/-! Actual periodic Riesz ranges for EVERY original COMPLEX H^-1 source,
with all associated vectors and the ENTIRE original H1 domain retained. -/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- The actual projection fixes every full physical root vector inside its circle,
including generalized vectors for complex potentials. -/
theorem singularHillRieszProjection_root_inside (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hc : sphere c ρ ⊆ singularHillResolventSet q) (a : ℂ)
    (ha : a ∈ singularHillResolventSet q) (z : ℂ) (hz : z ∈ ball c ρ)
    (x : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (hx : x ∈ singularHillRootSpaceTop q z) :
    singularHillRieszProjection q c ρ x = x := by
  by_cases hza : z = a
  · subst z
    rw [singularHillRootSpaceTop_eq_bot_of_mem_resolvent q a ha] at hx
    have hx0 : x = 0 := hx
    rw [hx0, map_zero]
  let P := singularHillRieszProjection q c ρ
  let T : Module.End ℂ (FourierLebesgueSpace (2:ℝ) (-1) 2) :=
    (singularHillBaseResolvent q a).toLinearMap
  have hP : IsIdempotentElem P.toLinearMap := congrArg ContinuousLinearMap.toLinearMap
    (isIdempotentElem_singularHillRieszProjection q c ρ hρ hc)
  have hPT : Commute P.toLinearMap T := congrArg ContinuousLinearMap.toLinearMap
    (commute_singularHillRieszProjection_resolvent q c ρ hρ.le hc a ha).eq
  apply NLS.FunctionalAnalysis.idempotent_eq_self_on_genEigenspace_top
    P.toLinearMap T hP hPT (z-a)⁻¹ _ x
      (by rwa [singularHillRootSpaceTop_eq_resolvent q a z ha hza] at hx)
  intro y hy
  have hm : y ∈ singularHillRootSpace q z 1 := by
    rw [singularHillRootSpace_eq_resolvent q a z ha hza]
    exact Module.End.mem_genEigenspace_one.mpr hy
  obtain ⟨f, hfy, hf⟩ := (mem_singularHillRootSpace_one _ z y).mp hm
  change singularHillRieszProjection q c ρ y = y
  rw [← hfy]
  exact singularHillRieszProjection_eigenvector_inside q c ρ hρ hc z hz f hf

/-- Outside the closed disk the actual projection kills the entire physical
algebraic root space, without a reality or semisimplicity hypothesis. -/
theorem singularHillRieszProjection_root_outside (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hc : sphere c ρ ⊆ singularHillResolventSet q) (a : ℂ)
    (ha : a ∈ singularHillResolventSet q) (z : ℂ) (hz : z ∉ closedBall c ρ)
    (x : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (hx : x ∈ singularHillRootSpaceTop q z) :
    singularHillRieszProjection q c ρ x = 0 := by
  by_cases hza : z = a
  · subst z
    rw [singularHillRootSpaceTop_eq_bot_of_mem_resolvent q a ha] at hx
    have hx0 : x = 0 := hx
    rw [hx0, map_zero]
  let P := singularHillRieszProjection q c ρ
  let T : Module.End ℂ (FourierLebesgueSpace (2:ℝ) (-1) 2) :=
    (singularHillBaseResolvent q a).toLinearMap
  have hP : IsIdempotentElem P.toLinearMap := congrArg ContinuousLinearMap.toLinearMap
    (isIdempotentElem_singularHillRieszProjection q c ρ hρ hc)
  have hPT : Commute P.toLinearMap T := congrArg ContinuousLinearMap.toLinearMap
    (commute_singularHillRieszProjection_resolvent q c ρ hρ.le hc a ha).eq
  apply NLS.FunctionalAnalysis.idempotent_eq_zero_on_genEigenspace_top
    P.toLinearMap T hP hPT (z-a)⁻¹ _ x
      (by rwa [singularHillRootSpaceTop_eq_resolvent q a z ha hza] at hx)
  intro y hy
  have hm : y ∈ singularHillRootSpace q z 1 := by
    rw [singularHillRootSpace_eq_resolvent q a z ha hza]
    exact Module.End.mem_genEigenspace_one.mpr hy
  obtain ⟨f, hfy, hf⟩ := (mem_singularHillRootSpace_one _ z y).mp hm
  change singularHillRieszProjection q c ρ y = 0
  rw [← hfy]
  exact singularHillRieszProjection_eigenvector_outside q c ρ hρ hc z hz f hf

/-- For every complex original potential, the actual Riesz range is precisely
the sum of all enclosed full physical algebraic root spaces. -/
theorem singularHillRieszProjection_range_eq_roots_complex (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hc : sphere c ρ ⊆ singularHillResolventSet q) (a : ℂ)
    (ha : a ∈ singularHillResolventSet q) :
    (singularHillRieszProjection q c ρ).range =
      ⨆ z : ball c ρ, singularHillRootSpaceTop
        q z.val := by
  let P := singularHillRieszProjection q c ρ
  let K : Module.End ℂ (FourierLebesgueSpace (2:ℝ) (-1) 2) :=
    (singularHillBaseResolvent q a).toLinearMap
  let W := P.range
  let := finiteDimensional_singularHillRieszProjection_range q c ρ hρ hc
  have hP := isIdempotentElem_singularHillRieszProjection q c ρ hρ hc
  have hfix (x : FourierLebesgueSpace (2:ℝ) (-1) 2) (hx : x ∈ W) : P x = x := by
    obtain ⟨y, rfl⟩ := hx
    exact congrArg (fun T : FourierLebesgueSpace (2:ℝ) (-1) 2 →L[ℂ]
      FourierLebesgueSpace (2:ℝ) (-1) 2 => T y) hP
  have hW : ∀ x ∈ W, K x ∈ W :=
    singularHillRieszProjection_range_invariant q c ρ hρ.le hc a ha
  apply le_antisymm
  · change W ≤ _
    rw [NLS.FunctionalAnalysis.eq_iSup_inf_genEigenspace_of_finite K W hW]
    apply iSup_le
    intro μ
    by_cases hμ : μ = 0
    · subst μ
      rw [NLS.FunctionalAnalysis.genEigenspace_zero_eq_bot_of_injective K
        (singularHillBaseResolvent_injective q a ha), inf_bot_eq]
      exact bot_le
    · let z := a+μ⁻¹
      have hza : z ≠ a := by dsimp [z]; simpa using inv_ne_zero hμ
      have he : (z-a)⁻¹ = μ := by simp [z]
      have hroot : K.genEigenspace μ ⊤ =
          singularHillRootSpaceTop q z := by
        rw [singularHillRootSpaceTop_eq_resolvent q a z ha hza, he]
      intro x hx
      have hxroot := hroot ▸ hx.2
      by_cases hz : z ∈ ball c ρ
      · exact (le_iSup (fun z : ball c ρ => singularHillRootSpaceTop
          q z.val) ⟨z, hz⟩) hxroot
      have hx0 : x = 0 := by
        by_cases hzclosed : z ∈ closedBall c ρ
        · have hzsphere : z ∈ sphere c ρ := mem_sphere.mpr
            (le_antisymm (mem_closedBall.mp hzclosed) (not_lt.mp hz))
          rw [singularHillRootSpaceTop_eq_bot_of_mem_resolvent q z (hc hzsphere)] at hxroot
          exact hxroot
        · exact (hfix x hx.1).symm.trans
            (singularHillRieszProjection_root_outside q c ρ hρ hc a ha z hzclosed x hxroot)
      exact hx0 ▸ Submodule.zero_mem _
  · apply iSup_le
    intro z x hx
    exact ⟨x, singularHillRieszProjection_root_inside q c ρ hρ hc a ha z.val z.property x hx⟩

end NLS.KdV
