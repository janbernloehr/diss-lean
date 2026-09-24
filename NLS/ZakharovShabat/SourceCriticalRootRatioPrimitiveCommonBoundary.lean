import NLS.ZakharovShabat.SourceCriticalRootRatioPrimitiveVerticalLimit
import NLS.ZakharovShabat.SourceCriticalRootRatioEndpointDogleg
import NLS.ZakharovShabat.SourceCriticalRootRatioHorizontalLimit
import NLS.ZakharovShabat.SourceGapStadiumAffine

/-!
# Matching boundary values at the two endpoints of an open gap

Each half-plane primitive has finite limits along the vertical rays
approaching the gap endpoints. The difference of its values along a
shifted horizontal segment is the quotient integral, which tends to
zero as the segment approaches the real gap. Thus the two ray limits
coincide within each half-plane.
-/

noncomputable section
open Set Filter Topology Complex
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A primitive above an open real gap has the same vertical-ray
boundary value at the gap's left and right endpoints. -/
theorem sourceCriticalRootRatio_upperPrimitive_common_vertical_limit
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, 0 < z.im →
      HasDerivAt F
        (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
          sourceCanonicalRoot hp hp1 ψ z) z) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    ∃ A : ℂ,
      Tendsto (fun y : ℝ => F (l+(y:ℂ)*Complex.I))
        (𝓝[>] (0:ℝ)) (𝓝 A) ∧
      Tendsto (fun y : ℝ => F (r+(y:ℂ)*Complex.I))
        (𝓝[>] (0:ℝ)) (𝓝 A) := by
  dsimp only
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  obtain ⟨ε,hε,hray⟩ :=
    exists_sourceCriticalRootRatio_upperPrimitive_vertical_limit
      hp hp1 ψ hreal n hopen
  obtain ⟨Aleft,hleft,_⟩ := hray (-1) (by simp) F hF
  obtain ⟨Aright,hright,_⟩ := hray 1 (by simp) F hF
  rw [sourceCanonicalRootGapPoint_neg_one_eq_left hp hp1 ψ n] at hleft
  rw [sourceCanonicalRootGapPoint_one_eq_right hp hp1 ψ n] at hright
  obtain ⟨hl,hr⟩ := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
    (isRealType_periodOnePotential ψ hreal) n
  have hcross (y : ℝ) (hy : 0 < y) :
      sourceCriticalRootRatio_horizontalIntegral hp hp1 ψ n y =
        F (r+(y:ℂ)*Complex.I) - F (l+(y:ℂ)*Complex.I) := by
    let γ := Path.segment (l+(y:ℂ)*Complex.I) (r+(y:ℂ)*Complex.I)
    have hγU (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
        0 < (γ.extend t).im := by
      rw [Path.extend_apply γ ht]
      have hseg : γ ⟨t,ht⟩ ∈
          segment ℝ (l+(y:ℂ)*Complex.I) (r+(y:ℂ)*Complex.I) := by
        rw [← Path.range_segment]
        exact ⟨⟨t,ht⟩,rfl⟩
      rw [sourceHorizontalSegment_im_eq l r hl hr y _ hseg]
      exact hy
    have hint : CurveIntegrable
        (NLS.ComplexAnalysis.holomorphicOneForm
          (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
            sourceCanonicalRoot hp hp1 ψ w)) γ :=
      sourceCriticalRootRatio_horizontalSegment_curveIntegrable
        hp hp1 ψ hreal n y (ne_of_gt hy)
    calc
      sourceCriticalRootRatio_horizontalIntegral hp hp1 ψ n y =
          ∫ᶜ z in γ, NLS.ComplexAnalysis.holomorphicOneForm
            (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
              sourceCanonicalRoot hp hp1 ψ w) z :=
        (sourceCriticalRootRatio_horizontalSegment_curveIntegral_eq hp hp1 ψ n y).symm
      _ = F (r+(y:ℂ)*Complex.I) - F (l+(y:ℂ)*Complex.I) :=
        NLS.ComplexAnalysis.curveIntegral_eq_sub_of_primitive _ F
          {z : ℂ | 0 < z.im} (fun z hz => hF z hz) γ
          ((sourceSegmentPath_contDiffOn_two _ _).of_le (by norm_num))
          hγU hint
  have hsub : Tendsto
      (fun y : ℝ => F (r+(y:ℂ)*Complex.I) - F (l+(y:ℂ)*Complex.I))
      (𝓝[>] (0:ℝ)) (𝓝 (Aright-Aleft)) := hright.sub hleft
  have hEq : (sourceCriticalRootRatio_horizontalIntegral hp hp1 ψ n) =ᶠ[𝓝[>] (0:ℝ)]
      (fun y : ℝ => F (r+(y:ℂ)*Complex.I) - F (l+(y:ℂ)*Complex.I)) := by
    filter_upwards [Ioo_mem_nhdsGT hε] with y hy
    exact hcross y hy.1
  have hlim := hsub.congr' hEq.symm
  have hlim0 := sourceCriticalRootRatio_horizontalIntegral_tendsto_zero_upper
    hp hp1 ψ hreal n hopen
  have hzero : Aright-Aleft = 0 := tendsto_nhds_unique hlim hlim0
  have heq : Aright = Aleft := sub_eq_zero.mp hzero
  refine ⟨Aleft,?_,?_⟩
  · simpa only [l] using hleft
  · simpa only [r,heq] using hright

/-- The two downward vertical-ray limits of a primitive below an open
real gap also coincide. -/
theorem sourceCriticalRootRatio_lowerPrimitive_common_vertical_limit
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, z.im < 0 →
      HasDerivAt F
        (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
          sourceCanonicalRoot hp hp1 ψ z) z) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    ∃ A : ℂ,
      Tendsto (fun y : ℝ => F (l+((-y:ℝ):ℂ)*Complex.I))
        (𝓝[>] (0:ℝ)) (𝓝 A) ∧
      Tendsto (fun y : ℝ => F (r+((-y:ℝ):ℂ)*Complex.I))
        (𝓝[>] (0:ℝ)) (𝓝 A) := by
  dsimp only
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  obtain ⟨ε,hε,hray⟩ :=
    exists_sourceCriticalRootRatio_lowerPrimitive_vertical_limit
      hp hp1 ψ hreal n hopen
  obtain ⟨Aleft,hleft,_⟩ := hray (-1) (by simp) F hF
  obtain ⟨Aright,hright,_⟩ := hray 1 (by simp) F hF
  rw [sourceCanonicalRootGapPoint_neg_one_eq_left hp hp1 ψ n] at hleft
  rw [sourceCanonicalRootGapPoint_one_eq_right hp hp1 ψ n] at hright
  obtain ⟨hl,hr⟩ := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
    (isRealType_periodOnePotential ψ hreal) n
  have hcross (y : ℝ) (hy : y < 0) :
      sourceCriticalRootRatio_horizontalIntegral hp hp1 ψ n y =
        F (r+(y:ℂ)*Complex.I) - F (l+(y:ℂ)*Complex.I) := by
    let γ := Path.segment (l+(y:ℂ)*Complex.I) (r+(y:ℂ)*Complex.I)
    have hγU (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
        (γ.extend t).im < 0 := by
      rw [Path.extend_apply γ ht]
      have hseg : γ ⟨t,ht⟩ ∈
          segment ℝ (l+(y:ℂ)*Complex.I) (r+(y:ℂ)*Complex.I) := by
        rw [← Path.range_segment]
        exact ⟨⟨t,ht⟩,rfl⟩
      rw [sourceHorizontalSegment_im_eq l r hl hr y _ hseg]
      exact hy
    have hint : CurveIntegrable
        (NLS.ComplexAnalysis.holomorphicOneForm
          (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
            sourceCanonicalRoot hp hp1 ψ w)) γ :=
      sourceCriticalRootRatio_horizontalSegment_curveIntegrable
        hp hp1 ψ hreal n y (ne_of_lt hy)
    calc
      sourceCriticalRootRatio_horizontalIntegral hp hp1 ψ n y =
          ∫ᶜ z in γ, NLS.ComplexAnalysis.holomorphicOneForm
            (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
              sourceCanonicalRoot hp hp1 ψ w) z :=
        (sourceCriticalRootRatio_horizontalSegment_curveIntegral_eq hp hp1 ψ n y).symm
      _ = F (r+(y:ℂ)*Complex.I) - F (l+(y:ℂ)*Complex.I) :=
        NLS.ComplexAnalysis.curveIntegral_eq_sub_of_primitive _ F
          {z : ℂ | z.im < 0} (fun z hz => hF z hz) γ
          ((sourceSegmentPath_contDiffOn_two _ _).of_le (by norm_num))
          hγU hint
  have hsub : Tendsto
      (fun y : ℝ => F (r+((-y:ℝ):ℂ)*Complex.I) -
        F (l+((-y:ℝ):ℂ)*Complex.I))
      (𝓝[>] (0:ℝ)) (𝓝 (Aright-Aleft)) := hright.sub hleft
  have hEq : (fun y : ℝ => sourceCriticalRootRatio_horizontalIntegral hp hp1 ψ n (-y))
      =ᶠ[𝓝[>] (0:ℝ)]
      (fun y : ℝ => F (r+((-y:ℝ):ℂ)*Complex.I) -
        F (l+((-y:ℝ):ℂ)*Complex.I)) := by
    filter_upwards [Ioo_mem_nhdsGT hε] with y hy
    simpa only [Complex.ofReal_neg] using hcross (-y) (neg_lt_zero.mpr hy.1)
  have hlim := hsub.congr' hEq.symm
  have hlim0 : Tendsto
      (fun y : ℝ => sourceCriticalRootRatio_horizontalIntegral hp hp1 ψ n (-y))
      (𝓝[>] (0:ℝ)) (𝓝 (0:ℂ)) := by
    simpa only [Function.comp_def, neg_zero] using
      (sourceCriticalRootRatio_horizontalIntegral_tendsto_zero_lower
        hp hp1 ψ hreal n hopen).comp tendsto_neg_nhdsGT_neg
  have hzero : Aright-Aleft = 0 := tendsto_nhds_unique hlim hlim0
  have heq : Aright = Aleft := sub_eq_zero.mp hzero
  refine ⟨Aleft,?_,?_⟩
  · simpa only [l] using hleft
  · simpa only [r,heq] using hright

end NLS.ZakharovShabat
