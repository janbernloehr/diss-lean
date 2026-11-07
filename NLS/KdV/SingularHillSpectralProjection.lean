import NLS.KdV.SingularHillAlgebraicMultiplicity
import NLS.KdV.PseudomeasureRieszRange

/-! Actual spectral projections and full physical root-space ranges for
arbitrary original H-minus-one potentials. Original H1 domain throughout. -/
noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- Norm analyticity in the spectral parameter at every original resolvent point. -/
theorem analyticAt_singularHillBaseResolvent (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (z : ℂ) (hz : z ∈ singularHillResolventSet q) :
    AnalyticAt ℂ (singularHillBaseResolvent q) z :=
  (analyticAt_singularHillBaseResolvent_joint (q,z) hz).comp
    (f := fun z : ℂ => (q,z)) (analyticAt_const.prod analyticAt_id)

/-- The actual original-domain inverses satisfy the full resolvent identity. -/
theorem singularHillResolventToH1_sub_apply (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z a : ℂ)
    (hz : z ∈ singularHillResolventSet q) (ha : a ∈ singularHillResolventSet q)
    (g : FourierLebesgueSpace (2:ℝ) (-1) 2) :
    singularHillResolventToH1 q z g - singularHillResolventToH1 q a g =
      (z-a) • singularHillResolventToH1 q z
        (singularHillDomainInclusion (singularHillResolventToH1 q a g)) := by
  let f := singularHillResolventToH1 q a g
  have hP := singularHillResolventToH1_right q a ha g
  have hcross : singularHillOperator q f -
      z • singularHillDomainInclusion f = g + (a-z) • singularHillDomainInclusion f := by
    change singularHillOperator q f -
      a • singularHillDomainInclusion f = g at hP
    rw [← hP]
    module
  have h := singularHillResolventToH1_left q z hz f
  rw [hcross, map_add, map_smul] at h
  change singularHillResolventToH1 q z g - f = _
  rw [← h]
  module

/-- The compact original H-minus-one resolvents obey the physical resolvent identity. -/
theorem singularHillBaseResolvent_sub (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z a : ℂ)
    (hz : z ∈ singularHillResolventSet q) (ha : a ∈ singularHillResolventSet q) :
    singularHillBaseResolvent q z - singularHillBaseResolvent q a =
      (z-a) • (singularHillBaseResolvent q z).comp (singularHillBaseResolvent q a) := by
  apply ContinuousLinearMap.ext
  intro g
  have h := congrArg singularHillDomainInclusion
    (singularHillResolventToH1_sub_apply q z a hz ha g)
  rw [map_sub, map_smul] at h
  exact h

/-- The negative of the original (L-z) inverse has the conventional (z-L) orientation. -/
theorem singularHill_oriented_resolvent_identity (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z w : ℂ)
    (hz : z ∈ singularHillResolventSet q) (hw : w ∈ singularHillResolventSet q) :
    -singularHillBaseResolvent q z-(-singularHillBaseResolvent q w) =
      (w-z) • ((-singularHillBaseResolvent q z)*(-singularHillBaseResolvent q w)) := by
  rw [neg_mul_neg,neg_sub_neg,← neg_sub,singularHillBaseResolvent_sub q z w hz hw,
    ← neg_smul,neg_sub]
  rfl


/-- A circle in the full physical resolvent defines an actual idempotent. -/
theorem isIdempotentElem_singularHillRieszProjection (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hc : sphere c ρ ⊆ singularHillResolventSet q) :
    IsIdempotentElem (singularHillRieszProjection q c ρ) := by
  apply CircleIntegral.isIdempotentElem_normalized_resolvent_of_open _
    (singularHillResolventSet q) (isOpen_singularHillResolventSet q) c ρ hρ hc
  · intro z hz
    exact (analyticAt_singularHillBaseResolvent q z hz).neg
  · exact fun z hz w hw => singularHill_oriented_resolvent_identity q z w hz hw

/-- The actual singular Riesz projection is compact in the original base norm. -/
theorem isCompactOperator_singularHillRieszProjection (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hc : sphere c ρ ⊆ singularHillResolventSet q) :
    IsCompactOperator (singularHillRieszProjection q c ρ) := by
  apply CircleIntegral.isCompactOperator_normalized hρ
  · intro z hz
    exact ((analyticAt_singularHillBaseResolvent q z (hc hz)).neg).continuousAt.continuousWithinAt
  · exact fun z _ => (isCompactOperator_singularHillBaseResolvent q z).neg

/-- Its spectral range is genuinely finite dimensional on the original H-minus-one space. -/
theorem finiteDimensional_singularHillRieszProjection_range (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hc : sphere c ρ ⊆ singularHillResolventSet q) :
    FiniteDimensional ℂ (singularHillRieszProjection q c ρ).range :=
  CircleIntegral.finiteDimensional_range_of_compact_idempotent _
    (isIdempotentElem_singularHillRieszProjection q c ρ hρ hc)
    (isCompactOperator_singularHillRieszProjection q c ρ hρ.le hc)

/-- An actual physical eigenvector enclosed by the circle lies in the projection range. -/
theorem singularHillRieszProjection_eigenvector_inside (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hc : sphere c ρ ⊆ singularHillResolventSet q)
    (μ : ℂ) (hμ : μ ∈ ball c ρ) (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : singularHillOperator q f =
      μ • singularHillDomainInclusion f) :
    singularHillRieszProjection q c ρ (singularHillDomainInclusion f) =
      singularHillDomainInclusion f := by
  have hint : CircleIntegrable (fun z => -singularHillBaseResolvent q z) c ρ :=
    (show ContinuousOn (fun z => -singularHillBaseResolvent q z) (sphere c ρ) from
      fun z hz => ((analyticAt_singularHillBaseResolvent q z (hc hz)).neg).continuousAt.continuousWithinAt).circleIntegrable hρ.le
  change (2*Real.pi*Complex.I:ℂ)⁻¹ •
    ((∮ z in C(c,ρ), -singularHillBaseResolvent q z) (singularHillDomainInclusion f)) = _
  rw [CircleIntegral.apply hint]
  have he : (∮ z in C(c,ρ), (-singularHillBaseResolvent q z) (singularHillDomainInclusion f)) =
      ∮ z in C(c,ρ), (z-μ)⁻¹ • singularHillDomainInclusion f := by
    apply circleIntegral.integral_congr hρ.le
    intro z hz
    have hμz : μ ≠ z := fun he => by
      rw [he] at hμ
      exact not_lt.mpr (mem_sphere.mp hz).ge hμ
    change -(singularHillBaseResolvent q z (singularHillDomainInclusion f)) = _
    rw [singularHillBaseResolvent_eigenvector q z μ (hc hz) hμz f hf,
      ← neg_smul,← inv_neg,neg_sub]
  rw [he,circleIntegral.integral_smul_const,circleIntegral.integral_sub_inv_of_mem_ball hμ,
    smul_smul,inv_mul_cancel₀,one_smul]
  simp [Real.pi_ne_zero]

/-- Every actual physical eigenvector outside the disk is annihilated by the projection. -/
theorem singularHillRieszProjection_eigenvector_outside (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hc : sphere c ρ ⊆ singularHillResolventSet q)
    (μ : ℂ) (hμ : μ ∉ closedBall c ρ) (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : singularHillOperator q f =
      μ • singularHillDomainInclusion f) :
    singularHillRieszProjection q c ρ (singularHillDomainInclusion f) = 0 := by
  have hint : CircleIntegrable (fun z => -singularHillBaseResolvent q z) c ρ :=
    (show ContinuousOn (fun z => -singularHillBaseResolvent q z) (sphere c ρ) from
      fun z hz => ((analyticAt_singularHillBaseResolvent q z (hc hz)).neg).continuousAt.continuousWithinAt).circleIntegrable hρ.le
  change (2*Real.pi*Complex.I:ℂ)⁻¹ •
    ((∮ z in C(c,ρ), -singularHillBaseResolvent q z) (singularHillDomainInclusion f)) = _
  rw [CircleIntegral.apply hint]
  have he : (∮ z in C(c,ρ), (-singularHillBaseResolvent q z) (singularHillDomainInclusion f)) =
      ∮ z in C(c,ρ), (z-μ)⁻¹ • singularHillDomainInclusion f := by
    apply circleIntegral.integral_congr hρ.le
    intro z hz
    have hμz : μ ≠ z := (ne_of_mem_of_not_mem (sphere_subset_closedBall hz) hμ).symm
    change -(singularHillBaseResolvent q z (singularHillDomainInclusion f)) = _
    rw [singularHillBaseResolvent_eigenvector q z μ (hc hz) hμz f hf,
      ← neg_smul,← inv_neg,neg_sub]
  rw [he,circleIntegral.integral_smul_const,CircleIntegral.integral_sub_inv_eq_zero hρ.le hμ,
    zero_smul,smul_zero]


/-- Every actual compact base resolvent is injective on the entire original base space. -/
theorem singularHillBaseResolvent_injective (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (a : ℂ)
    (ha : a ∈ singularHillResolventSet q) :
    Function.Injective (singularHillBaseResolvent q a) := by
  change Function.Injective (singularHillBaseResolvent q a).toLinearMap
  rw [← pencilResolvent_singularHillPencilEquiv q a ha]
  exact NLS.FunctionalAnalysis.pencilResolvent_injective _
    singularHillDomainInclusion_injective _

/-- Actual base resolvents at two physical resolvent points commute. -/
theorem commute_singularHillBaseResolvent (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z a : ℂ)
    (hz : z ∈ singularHillResolventSet q) (ha : a ∈ singularHillResolventSet q) :
    Commute (singularHillBaseResolvent q z) (singularHillBaseResolvent q a) := by
  by_cases hza : z = a
  · subst z
    exact Commute.refl _
  have h₁ := singularHillBaseResolvent_sub q z a hz ha
  have h₂ := congrArg Neg.neg (singularHillBaseResolvent_sub q a z ha hz)
  rw [neg_sub,← neg_smul,neg_sub] at h₂
  have he := congrArg (fun T => (z-a)⁻¹ • T) (h₁.symm.trans h₂)
  change (singularHillBaseResolvent q z).comp (singularHillBaseResolvent q a) =
    (singularHillBaseResolvent q a).comp (singularHillBaseResolvent q z)
  simpa only [inv_smul_smul₀ (sub_ne_zero.mpr hza)] using he

/-- The operator-valued physical Riesz integral commutes with every actual base resolvent. -/
theorem commute_singularHillRieszProjection_resolvent (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (c : ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hc : sphere c ρ ⊆ singularHillResolventSet q) (a : ℂ)
    (ha : a ∈ singularHillResolventSet q) :
    Commute (singularHillRieszProjection q c ρ) (singularHillBaseResolvent q a) := by
  have hint : CircleIntegrable (fun z => -singularHillBaseResolvent q z) c ρ :=
    (show ContinuousOn (fun z => -singularHillBaseResolvent q z) (sphere c ρ) from
      fun z hz => ((analyticAt_singularHillBaseResolvent q z (hc hz)).neg).continuousAt.continuousWithinAt).circleIntegrable hρ
  change CircleIntegral.normalized _ c ρ * _ = _ * CircleIntegral.normalized _ c ρ
  unfold CircleIntegral.normalized
  rw [smul_mul_assoc,mul_smul_comm,
    CircleIntegral.integral_mul_const _ _ _ _ hint,
    CircleIntegral.integral_const_mul _ _ _ _ hint]
  congr 1
  apply circleIntegral.integral_congr hρ
  intro z hz
  change (-singularHillBaseResolvent q z)*singularHillBaseResolvent q a =
    singularHillBaseResolvent q a*(-singularHillBaseResolvent q z)
  rw [neg_mul,mul_neg]
  exact congrArg Neg.neg (commute_singularHillBaseResolvent q z a (hc hz) ha).eq

/-- The finite actual spectral range is invariant under every actual base resolvent. -/
theorem singularHillRieszProjection_range_invariant (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (c : ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hc : sphere c ρ ⊆ singularHillResolventSet q) (a : ℂ)
    (ha : a ∈ singularHillResolventSet q) :
    MapsTo (singularHillBaseResolvent q a)
      (singularHillRieszProjection q c ρ).range
      (singularHillRieszProjection q c ρ).range := by
  rintro x ⟨y,rfl⟩
  refine ⟨singularHillBaseResolvent q a y,?_⟩
  exact congrArg (fun T : FourierLebesgueSpace (2:ℝ) (-1) 2 →L[ℂ]
    FourierLebesgueSpace (2:ℝ) (-1) 2 => T y)
      (commute_singularHillRieszProjection_resolvent q c ρ hρ hc a ha).eq

/-- The compact-resolvent root-space transport also holds at the base parameter,
where both spaces are zero. -/
theorem singularHillRootSpaceTop_eq_resolvent_all (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (a z : ℂ)
    (ha : a ∈ singularHillResolventSet q) :
    singularHillRootSpaceTop q z =
      Module.End.genEigenspace (singularHillBaseResolvent q a).toLinearMap (z-a)⁻¹ ⊤ := by
  by_cases hza : z = a
  · subst z
    rw [singularHillRootSpaceTop_eq_bot_of_mem_resolvent q a ha,sub_self,inv_zero,
      NLS.FunctionalAnalysis.genEigenspace_zero_eq_bot_of_injective _
        (singularHillBaseResolvent_injective q a ha)]
  · exact singularHillRootSpaceTop_eq_resolvent q a z ha hza

/-- The full actual physical root spaces at distinct spectral parameters form an independent family. -/
theorem independent_singularHillRootSpaceTop (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (a : ℂ)
    (ha : a ∈ singularHillResolventSet q) :
    iSupIndep (fun z : ℂ => singularHillRootSpaceTop
      q z) := by
  simp_rw [singularHillRootSpaceTop_eq_resolvent_all q a _ ha]
  apply (Module.End.independent_genEigenspace (singularHillBaseResolvent q a).toLinearMap ⊤).comp
  intro z w he
  have h : z-a = w-a := inv_injective he
  linear_combination h

/-- On a real original potential, the actual Riesz range is exactly the sum of
all full physical algebraic root spaces enclosed by the circle. -/
theorem singularHillRieszProjection_range_eq_roots (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (hq : q.val =
      q.val.conjugate)
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
    obtain ⟨y,rfl⟩ := hx
    exact congrArg (fun T : FourierLebesgueSpace (2:ℝ) (-1) 2 →L[ℂ]
      FourierLebesgueSpace (2:ℝ) (-1) 2 => T y) hP
  have hW : ∀ x ∈ W, K x ∈ W := singularHillRieszProjection_range_invariant q c ρ hρ.le hc a ha
  apply le_antisymm
  · change W ≤ _
    rw [NLS.FunctionalAnalysis.eq_iSup_inf_genEigenspace_of_finite K W hW]
    apply iSup_le
    intro μ
    by_cases hμ : μ = 0
    · subst μ
      rw [NLS.FunctionalAnalysis.genEigenspace_zero_eq_bot_of_injective K
        (singularHillBaseResolvent_injective q a ha),inf_bot_eq]
      exact bot_le
    · let z := a+μ⁻¹
      have hza : z ≠ a := by dsimp [z]; simpa using inv_ne_zero hμ
      have he : (z-a)⁻¹ = μ := by simp [z]
      have hroot : K.genEigenspace μ ⊤ =
          singularHillRootSpaceTop q z := by
        rw [singularHillRootSpaceTop_eq_resolvent q a z ha hza,he]
      intro x hx
      have hxroot := hroot ▸ hx.2
      have hxone := hxroot
      rw [singularHillRootSpaceTop_eq_one_of_real _ hq z] at hxone
      obtain ⟨f,hfx,hf⟩ := (mem_singularHillRootSpace_one _ z x).mp hxone
      by_cases hx0 : x = 0
      · exact hx0 ▸ Submodule.zero_mem _
      have hzclosed : z ∈ closedBall c ρ := by
        by_contra hzout
        have hpzero := singularHillRieszProjection_eigenvector_outside q c ρ hρ hc z hzout f hf
        rw [hfx] at hpzero
        exact hx0 ((hfix x hx.1).symm.trans hpzero)
      have hzcircle : z ∉ sphere c ρ := by
        intro hz
        have hinj := (hc hz).1
        have hzero : (singularHillOperator q-
            z • singularHillDomainInclusion) f = 0 := sub_eq_zero.mpr hf
        have hfzero := hinj (hzero.trans (map_zero _).symm)
        exact hx0 (hfx.symm.trans (by rw [hfzero,map_zero]))
      have hzball : z ∈ ball c ρ := lt_of_le_of_ne (mem_closedBall.mp hzclosed)
        (fun he => hzcircle (mem_sphere.mpr he))
      exact (le_iSup (fun z : ball c ρ => singularHillRootSpaceTop
        q z.val) ⟨z,hzball⟩) hxroot
  · apply iSup_le
    intro z x hx
    rw [singularHillRootSpaceTop_eq_one_of_real _ hq z.val] at hx
    obtain ⟨f,hfx,hf⟩ := (mem_singularHillRootSpace_one _ z.val x).mp hx
    refine ⟨x,?_⟩
    rw [← hfx]
    exact singularHillRieszProjection_eigenvector_inside q c ρ hρ hc z.val z.property f hf

/-- A full original H-minus-one norm neighborhood preserves a valid physical
circle and the rank of its ACTUAL spectral projection, without endpoint
membership or reality assumptions on the nearby complex potentials. -/
theorem eventually_singularHillRieszProjection_rank_eq
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hc : sphere c ρ ⊆ singularHillResolventSet q) :
    ∀ᶠ v : FourierLebesgueSpace (2:ℝ) (-1) 2 in 𝓝 q,
      sphere c ρ ⊆ singularHillResolventSet v ∧
      Module.finrank ℂ (singularHillRieszProjection v c ρ).range =
        Module.finrank ℂ (singularHillRieszProjection q c ρ).range := by
  let U := {v : FourierLebesgueSpace (2:ℝ) (-1) 2 | sphere c ρ ⊆ singularHillResolventSet v}
  have hu : U ∈ 𝓝 q := (isOpen_singularHillResolventCircle c ρ).mem_nhds hc
  have hp := (continuousOn_singularHillRieszProjection id U continuous_id.continuousOn
    c ρ hρ.le (fun _ h => h)).continuousAt hu
  have he := hp.preimage_mem_nhds (Metric.ball_mem_nhds (singularHillRieszProjection q c ρ) zero_lt_one)
  filter_upwards [hu, he] with v hv hn
  refine ⟨hv, ?_⟩
  let : FiniteDimensional ℂ (singularHillRieszProjection q c ρ).range :=
    finiteDimensional_singularHillRieszProjection_range q c ρ hρ hc
  let : FiniteDimensional ℂ (singularHillRieszProjection v c ρ).range :=
    finiteDimensional_singularHillRieszProjection_range v c ρ hρ hv
  exact ProjectionRank.finrank_eq_of_norm_sub_lt_one _ _
    (isIdempotentElem_singularHillRieszProjection v c ρ hρ hv)
    (isIdempotentElem_singularHillRieszProjection q c ρ hρ hc)
    (by simpa only [mem_preimage, Metric.mem_ball, dist_eq_norm, Function.id_def] using hn)

end NLS.KdV
