import NLS.KdV.PseudomeasureRieszProjection
import NLS.KdV.PseudomeasureRealSpectrum
import NLS.FunctionalAnalysis.FiniteInvariantSpectrum

/-! The actual Riesz range and the original physical root spaces. -/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- Every actual compact base resolvent is injective on the entire original base space. -/
theorem endpointHillBaseResolvent_injective (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (a : ℂ)
    (ha : a ∈ endpointHillResolventSet r hr1 q) :
    Function.Injective (endpointHillBaseResolvent r hr1 q a) := by
  change Function.Injective (endpointHillBaseResolvent r hr1 q a).toLinearMap
  rw [← pencilResolvent_endpointHillPencilEquiv r hr1 q a ha]
  exact NLS.FunctionalAnalysis.pencilResolvent_injective _
    singularHillDomainInclusion_injective _

/-- Actual base resolvents at two physical resolvent points commute. -/
theorem commute_endpointHillBaseResolvent (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (z a : ℂ)
    (hz : z ∈ endpointHillResolventSet r hr1 q) (ha : a ∈ endpointHillResolventSet r hr1 q) :
    Commute (endpointHillBaseResolvent r hr1 q z) (endpointHillBaseResolvent r hr1 q a) := by
  by_cases hza : z = a
  · subst z
    exact Commute.refl _
  have h₁ := endpointHillBaseResolvent_sub r hr1 q z a hz ha
  have h₂ := congrArg Neg.neg (endpointHillBaseResolvent_sub r hr1 q a z ha hz)
  rw [neg_sub,← neg_smul,neg_sub] at h₂
  have he := congrArg (fun T => (z-a)⁻¹ • T) (h₁.symm.trans h₂)
  change (endpointHillBaseResolvent r hr1 q z).comp (endpointHillBaseResolvent r hr1 q a) =
    (endpointHillBaseResolvent r hr1 q a).comp (endpointHillBaseResolvent r hr1 q z)
  simpa only [inv_smul_smul₀ (sub_ne_zero.mpr hza)] using he

/-- The operator-valued physical Riesz integral commutes with every actual base resolvent. -/
theorem commute_endpointHillRieszProjection_resolvent (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (c : ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hc : sphere c ρ ⊆ endpointHillResolventSet r hr1 q) (a : ℂ)
    (ha : a ∈ endpointHillResolventSet r hr1 q) :
    Commute (endpointHillRieszProjection r hr1 q c ρ) (endpointHillBaseResolvent r hr1 q a) := by
  have hint : CircleIntegrable (fun z => -endpointHillBaseResolvent r hr1 q z) c ρ :=
    (show ContinuousOn (fun z => -endpointHillBaseResolvent r hr1 q z) (sphere c ρ) from
      fun z hz => ((analyticAt_endpointHillBaseResolvent r hr1 q z (hc hz)).neg).continuousAt.continuousWithinAt).circleIntegrable hρ
  change CircleIntegral.normalized _ c ρ * _ = _ * CircleIntegral.normalized _ c ρ
  unfold CircleIntegral.normalized
  rw [smul_mul_assoc,mul_smul_comm,
    CircleIntegral.integral_mul_const _ _ _ _ hint,
    CircleIntegral.integral_const_mul _ _ _ _ hint]
  congr 1
  apply circleIntegral.integral_congr hρ
  intro z hz
  change (-endpointHillBaseResolvent r hr1 q z)*endpointHillBaseResolvent r hr1 q a =
    endpointHillBaseResolvent r hr1 q a*(-endpointHillBaseResolvent r hr1 q z)
  rw [neg_mul,mul_neg]
  exact congrArg Neg.neg (commute_endpointHillBaseResolvent r hr1 q z a (hc hz) ha).eq

/-- The finite actual spectral range is invariant under every actual base resolvent. -/
theorem endpointHillRieszProjection_range_invariant (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (c : ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hc : sphere c ρ ⊆ endpointHillResolventSet r hr1 q) (a : ℂ)
    (ha : a ∈ endpointHillResolventSet r hr1 q) :
    MapsTo (endpointHillBaseResolvent r hr1 q a)
      (endpointHillRieszProjection r hr1 q c ρ).range
      (endpointHillRieszProjection r hr1 q c ρ).range := by
  rintro x ⟨y,rfl⟩
  refine ⟨endpointHillBaseResolvent r hr1 q a y,?_⟩
  exact congrArg (fun T : FourierLebesgueSpace (2:ℝ) (-1) 2 →L[ℂ]
    FourierLebesgueSpace (2:ℝ) (-1) 2 => T y)
      (commute_endpointHillRieszProjection_resolvent r hr1 q c ρ hρ hc a ha).eq

/-- The compact-resolvent root-space transport also holds at the base parameter,
where both spaces are zero. -/
theorem endpointHillRootSpaceTop_eq_resolvent_all (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (a z : ℂ)
    (ha : a ∈ endpointHillResolventSet r hr1 q) :
    singularHillRootSpaceTop (endpointHillHminusOne SpectralWeight.one r hr1 q) z =
      Module.End.genEigenspace (endpointHillBaseResolvent r hr1 q a).toLinearMap (z-a)⁻¹ ⊤ := by
  by_cases hza : z = a
  · subst z
    rw [endpointHillRootSpaceTop_eq_bot_of_mem_resolvent r hr1 q a ha,sub_self,inv_zero,
      NLS.FunctionalAnalysis.genEigenspace_zero_eq_bot_of_injective _
        (endpointHillBaseResolvent_injective r hr1 q a ha)]
  · exact endpointHillRootSpaceTop_eq_resolvent r hr1 q a z ha hza

/-- The full actual physical root spaces at distinct spectral parameters form an independent family. -/
theorem independent_endpointHillRootSpaceTop (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (a : ℂ)
    (ha : a ∈ endpointHillResolventSet r hr1 q) :
    iSupIndep (fun z : ℂ => singularHillRootSpaceTop
      (endpointHillHminusOne SpectralWeight.one r hr1 q) z) := by
  simp_rw [endpointHillRootSpaceTop_eq_resolvent_all r hr1 q a _ ha]
  apply (Module.End.independent_genEigenspace (endpointHillBaseResolvent r hr1 q a).toLinearMap ⊤).comp
  intro z w he
  have h : z-a = w-a := inv_injective he
  linear_combination h

/-- On a real original potential, the actual Riesz range is exactly the sum of
all full physical algebraic root spaces enclosed by the circle. -/
theorem endpointHillRieszProjection_range_eq_roots (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (hq : (endpointHillHminusOne SpectralWeight.one r hr1 q).val =
      (endpointHillHminusOne SpectralWeight.one r hr1 q).val.conjugate)
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
    obtain ⟨y,rfl⟩ := hx
    exact congrArg (fun T : FourierLebesgueSpace (2:ℝ) (-1) 2 →L[ℂ]
      FourierLebesgueSpace (2:ℝ) (-1) 2 => T y) hP
  have hW : ∀ x ∈ W, K x ∈ W := endpointHillRieszProjection_range_invariant r hr1 q c ρ hρ.le hc a ha
  apply le_antisymm
  · change W ≤ _
    rw [NLS.FunctionalAnalysis.eq_iSup_inf_genEigenspace_of_finite K W hW]
    apply iSup_le
    intro μ
    by_cases hμ : μ = 0
    · subst μ
      rw [NLS.FunctionalAnalysis.genEigenspace_zero_eq_bot_of_injective K
        (endpointHillBaseResolvent_injective r hr1 q a ha),inf_bot_eq]
      exact bot_le
    · let z := a+μ⁻¹
      have hza : z ≠ a := by dsimp [z]; simpa using inv_ne_zero hμ
      have he : (z-a)⁻¹ = μ := by simp [z]
      have hroot : K.genEigenspace μ ⊤ =
          singularHillRootSpaceTop (endpointHillHminusOne SpectralWeight.one r hr1 q) z := by
        rw [endpointHillRootSpaceTop_eq_resolvent r hr1 q a z ha hza,he]
      intro x hx
      have hxroot := hroot ▸ hx.2
      have hxone := hxroot
      rw [singularHillRootSpaceTop_eq_one_of_real _ hq z] at hxone
      obtain ⟨f,hfx,hf⟩ := (mem_singularHillRootSpace_one _ z x).mp hxone
      by_cases hx0 : x = 0
      · exact hx0 ▸ Submodule.zero_mem _
      have hzclosed : z ∈ closedBall c ρ := by
        by_contra hzout
        have hpzero := endpointHillRieszProjection_eigenvector_outside r hr1 q c ρ hρ hc z hzout f hf
        rw [hfx] at hpzero
        exact hx0 ((hfix x hx.1).symm.trans hpzero)
      have hzcircle : z ∉ sphere c ρ := by
        intro hz
        have hinj := (hc hz).1
        have hzero : (singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q)-
            z • singularHillDomainInclusion) f = 0 := sub_eq_zero.mpr hf
        have hfzero := hinj (hzero.trans (map_zero _).symm)
        exact hx0 (hfx.symm.trans (by rw [hfzero,map_zero]))
      have hzball : z ∈ ball c ρ := lt_of_le_of_ne (mem_closedBall.mp hzclosed)
        (fun he => hzcircle (mem_sphere.mpr he))
      exact (le_iSup (fun z : ball c ρ => singularHillRootSpaceTop
        (endpointHillHminusOne SpectralWeight.one r hr1 q) z.val) ⟨z,hzball⟩) hxroot
  · apply iSup_le
    intro z x hx
    rw [singularHillRootSpaceTop_eq_one_of_real _ hq z.val] at hx
    obtain ⟨f,hfx,hf⟩ := (mem_singularHillRootSpace_one _ z.val x).mp hx
    refine ⟨x,?_⟩
    rw [← hfx]
    exact endpointHillRieszProjection_eigenvector_inside r hr1 q c ρ hρ hc z.val z.property f hf

end NLS.KdV
