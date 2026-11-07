import NLS.KdV.PseudomeasureRieszRange
import NLS.FunctionalAnalysis.IdempotentRootSpaces

/-!
# Riesz projections and full root spaces for complex singular Hill potentials

The physical potential may be complex and its root chains need not be
semisimple. All chains retain the original H1 domain in H-minus-one.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- The actual projection fixes every full physical root vector inside its circle,
including generalized vectors for complex potentials. -/
theorem endpointHillRieszProjection_root_inside (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hc : sphere c ρ ⊆ endpointHillResolventSet r hr1 q) (a : ℂ)
    (ha : a ∈ endpointHillResolventSet r hr1 q) (z : ℂ) (hz : z ∈ ball c ρ)
    (x : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (hx : x ∈ singularHillRootSpaceTop (endpointHillHminusOne SpectralWeight.one r hr1 q) z) :
    endpointHillRieszProjection r hr1 q c ρ x = x := by
  by_cases hza : z = a
  · subst z
    rw [endpointHillRootSpaceTop_eq_bot_of_mem_resolvent r hr1 q a ha] at hx
    have hx0 : x = 0 := hx
    rw [hx0, map_zero]
  let P := endpointHillRieszProjection r hr1 q c ρ
  let T : Module.End ℂ (FourierLebesgueSpace (2:ℝ) (-1) 2) :=
    (endpointHillBaseResolvent r hr1 q a).toLinearMap
  have hP : IsIdempotentElem P.toLinearMap := congrArg ContinuousLinearMap.toLinearMap
    (isIdempotentElem_endpointHillRieszProjection r hr1 q c ρ hρ hc)
  have hPT : Commute P.toLinearMap T := congrArg ContinuousLinearMap.toLinearMap
    (commute_endpointHillRieszProjection_resolvent r hr1 q c ρ hρ.le hc a ha).eq
  apply NLS.FunctionalAnalysis.idempotent_eq_self_on_genEigenspace_top
    P.toLinearMap T hP hPT (z-a)⁻¹ _ x
      (by rwa [endpointHillRootSpaceTop_eq_resolvent r hr1 q a z ha hza] at hx)
  intro y hy
  have hm : y ∈ singularHillRootSpace (endpointHillHminusOne SpectralWeight.one r hr1 q) z 1 := by
    rw [endpointHillRootSpace_eq_resolvent r hr1 q a z ha hza]
    exact Module.End.mem_genEigenspace_one.mpr hy
  obtain ⟨f, hfy, hf⟩ := (mem_singularHillRootSpace_one _ z y).mp hm
  change endpointHillRieszProjection r hr1 q c ρ y = y
  rw [← hfy]
  exact endpointHillRieszProjection_eigenvector_inside r hr1 q c ρ hρ hc z hz f hf

/-- Outside the closed disk the actual projection kills the entire physical
algebraic root space, without a reality or semisimplicity hypothesis. -/
theorem endpointHillRieszProjection_root_outside (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hc : sphere c ρ ⊆ endpointHillResolventSet r hr1 q) (a : ℂ)
    (ha : a ∈ endpointHillResolventSet r hr1 q) (z : ℂ) (hz : z ∉ closedBall c ρ)
    (x : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (hx : x ∈ singularHillRootSpaceTop (endpointHillHminusOne SpectralWeight.one r hr1 q) z) :
    endpointHillRieszProjection r hr1 q c ρ x = 0 := by
  by_cases hza : z = a
  · subst z
    rw [endpointHillRootSpaceTop_eq_bot_of_mem_resolvent r hr1 q a ha] at hx
    have hx0 : x = 0 := hx
    rw [hx0, map_zero]
  let P := endpointHillRieszProjection r hr1 q c ρ
  let T : Module.End ℂ (FourierLebesgueSpace (2:ℝ) (-1) 2) :=
    (endpointHillBaseResolvent r hr1 q a).toLinearMap
  have hP : IsIdempotentElem P.toLinearMap := congrArg ContinuousLinearMap.toLinearMap
    (isIdempotentElem_endpointHillRieszProjection r hr1 q c ρ hρ hc)
  have hPT : Commute P.toLinearMap T := congrArg ContinuousLinearMap.toLinearMap
    (commute_endpointHillRieszProjection_resolvent r hr1 q c ρ hρ.le hc a ha).eq
  apply NLS.FunctionalAnalysis.idempotent_eq_zero_on_genEigenspace_top
    P.toLinearMap T hP hPT (z-a)⁻¹ _ x
      (by rwa [endpointHillRootSpaceTop_eq_resolvent r hr1 q a z ha hza] at hx)
  intro y hy
  have hm : y ∈ singularHillRootSpace (endpointHillHminusOne SpectralWeight.one r hr1 q) z 1 := by
    rw [endpointHillRootSpace_eq_resolvent r hr1 q a z ha hza]
    exact Module.End.mem_genEigenspace_one.mpr hy
  obtain ⟨f, hfy, hf⟩ := (mem_singularHillRootSpace_one _ z y).mp hm
  change endpointHillRieszProjection r hr1 q c ρ y = 0
  rw [← hfy]
  exact endpointHillRieszProjection_eigenvector_outside r hr1 q c ρ hρ hc z hz f hf

/-- For every complex original potential, the actual Riesz range is precisely
the sum of all enclosed full physical algebraic root spaces. -/
theorem endpointHillRieszProjection_range_eq_roots_complex (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hc : sphere c ρ ⊆ endpointHillResolventSet r hr1 q) (a : ℂ)
    (ha : a ∈ endpointHillResolventSet r hr1 q) :
    (endpointHillRieszProjection r hr1 q c ρ).range =
      ⨆ z : ball c ρ, singularHillRootSpaceTop
        (endpointHillHminusOne SpectralWeight.one r hr1 q) z.val := by
  let P := endpointHillRieszProjection r hr1 q c ρ
  let K : Module.End ℂ (FourierLebesgueSpace (2:ℝ) (-1) 2) :=
    (endpointHillBaseResolvent r hr1 q a).toLinearMap
  let W := P.range
  let := finiteDimensional_endpointHillRieszProjection_range r hr1 q c ρ hρ hc
  have hP := isIdempotentElem_endpointHillRieszProjection r hr1 q c ρ hρ hc
  have hfix (x : FourierLebesgueSpace (2:ℝ) (-1) 2) (hx : x ∈ W) : P x = x := by
    obtain ⟨y, rfl⟩ := hx
    exact congrArg (fun T : FourierLebesgueSpace (2:ℝ) (-1) 2 →L[ℂ]
      FourierLebesgueSpace (2:ℝ) (-1) 2 => T y) hP
  have hW : ∀ x ∈ W, K x ∈ W :=
    endpointHillRieszProjection_range_invariant r hr1 q c ρ hρ.le hc a ha
  apply le_antisymm
  · change W ≤ _
    rw [NLS.FunctionalAnalysis.eq_iSup_inf_genEigenspace_of_finite K W hW]
    apply iSup_le
    intro μ
    by_cases hμ : μ = 0
    · subst μ
      rw [NLS.FunctionalAnalysis.genEigenspace_zero_eq_bot_of_injective K
        (endpointHillBaseResolvent_injective r hr1 q a ha), inf_bot_eq]
      exact bot_le
    · let z := a+μ⁻¹
      have hza : z ≠ a := by dsimp [z]; simpa using inv_ne_zero hμ
      have he : (z-a)⁻¹ = μ := by simp [z]
      have hroot : K.genEigenspace μ ⊤ =
          singularHillRootSpaceTop (endpointHillHminusOne SpectralWeight.one r hr1 q) z := by
        rw [endpointHillRootSpaceTop_eq_resolvent r hr1 q a z ha hza, he]
      intro x hx
      have hxroot := hroot ▸ hx.2
      by_cases hz : z ∈ ball c ρ
      · exact (le_iSup (fun z : ball c ρ => singularHillRootSpaceTop
          (endpointHillHminusOne SpectralWeight.one r hr1 q) z.val) ⟨z, hz⟩) hxroot
      have hx0 : x = 0 := by
        by_cases hzclosed : z ∈ closedBall c ρ
        · have hzsphere : z ∈ sphere c ρ := mem_sphere.mpr
            (le_antisymm (mem_closedBall.mp hzclosed) (not_lt.mp hz))
          rw [endpointHillRootSpaceTop_eq_bot_of_mem_resolvent r hr1 q z (hc hzsphere)] at hxroot
          exact hxroot
        · exact (hfix x hx.1).symm.trans
            (endpointHillRieszProjection_root_outside r hr1 q c ρ hρ hc a ha z hzclosed x hxroot)
      exact hx0 ▸ Submodule.zero_mem _
  · apply iSup_le
    intro z x hx
    exact ⟨x, endpointHillRieszProjection_root_inside r hr1 q c ρ hρ hc a ha z.val z.property x hx⟩

end NLS.KdV
