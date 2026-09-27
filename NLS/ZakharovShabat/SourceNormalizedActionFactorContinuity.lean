import NLS.ZakharovShabat.SourceCriticalDisplacementContinuity
import NLS.ZakharovShabat.SourceNormalizedActionCollapseEstimate
import NLS.ZakharovShabat.SourceCanonicalRootGapIsolation

/-!
# Uniform continuity of the deleted factor at a collapsed gap

The factor in the cosine action formula is a joint analytic quotient
of the spectral variable, the critical-root displacement sequence,
and the source. At a collapsed real-type gap, its cosine path shrinks
to the periodic midpoint. Norm continuity of the full displacement
sequence makes joint continuity applicable uniformly in the cosine
parameter.
-/

noncomputable section
open Set Complex Filter Topology Metric NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- At a real-type source, a nonzero periodic gap is an open real
interval between the ordered canonical endpoints. -/
theorem source_openRealGap_of_realType_gap_ne_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (hgap : sourcePeriodicGapDisplacement hp hp1 ψ n ≠ 0) :
    (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
    (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re := by
  let L := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let R := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  have hle : L.re ≤ R.re :=
    re_le_of_complexLexLE ((canonicalPeriodicEndpoints_spec hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ)).2.1 n)
  obtain ⟨hLim,hRim⟩ := canonicalPeriodicEndpoints_im_eq_zero_of_realType
    hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
      (isRealType_periodOnePotential ψ hreal) n
  have hne : L.re ≠ R.re := by
    intro he
    have hLR : L = R := by
      apply Complex.ext
      · exact he
      · rw [hLim,hRim]
    apply hgap
    simp only [sourcePeriodicGapDisplacement_apply, canonicalPeriodicGap]
    change R-L = 0
    rw [hLR]
    simp
  change L.re < R.re
  exact lt_of_le_of_ne hle hne

/-- As a real-type gap collapses, the regular factor converges
uniformly along the entire cosine-parametrized gap. -/
theorem eventually_uniform_sourceCriticalRootRatioExtension_cosine_of_collapsedGap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (hgap : sourcePeriodicGapDisplacement hp hp1 φ n = 0) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ ψ : CoeffPair p in 𝓝 φ,
      ∀ θ : ℝ,
        ‖I * sourceCriticalRootRatioExtension hp hp1 n ψ
          (sourceStandardRootMidpoint hp hp1 ψ n +
            sourceStandardRootHalfGap hp hp1 ψ n * (Real.cos θ:ℂ)) -
          I * sourceCriticalRootRatioExtension hp hp1 n φ
            (sourceStandardRootMidpoint hp hp1 φ n)‖ < ε := by
  let τ (ψ : CoeffPair p) := sourceStandardRootMidpoint hp hp1 ψ n
  let δ (ψ : CoeffPair p) := sourceStandardRootHalfGap hp hp1 ψ n
  let a (ψ : CoeffPair p) := sourceCriticalDisplacement hp hp1 ψ
  let Q := sourceSingleRootQuotientJointProduct hp hp1 n
  let t : ℂ × (Coeff p × CoeffPair p) := (τ φ,(a φ,φ))
  obtain ⟨W₁,_,_,hW₁real,hdata⟩ :=
    exists_global_source_analytic_singleRootQuotient hp hp1
  obtain ⟨W₂,_,_,hW₂real,hpoint⟩ :=
    exists_global_source_gapPoint_mem_omittedDomain hp hp1
  have hτdom : τ φ ∈ sourceStandardRootOmittedDomain hp hp1 φ n := by
    have h := hpoint φ (hW₂real hreal) n 0 (by norm_num) (by norm_num)
    simpa [sourceCanonicalRootGapPoint, τ, δ] using h
  have ht : t ∈ sourceSingleRootQuotientJointDomain hp hp1 W₁ n :=
    ⟨hW₁real hreal,hτdom⟩
  have hQ : ContinuousAt Q t := ((hdata n).2 t ht).continuousAt
  have hL := continuousAt_canonicalPeriodicLeft_periodOne_of_realType
    hp hp1 φ hreal n
  have hR := continuousAt_canonicalPeriodicRight_periodOne_of_realType
    hp hp1 φ hreal n
  have hτ : ContinuousAt τ φ := by
    change ContinuousAt (fun ψ : CoeffPair p =>
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n +
       canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n)/2) φ
    exact (hL.add hR).div_const 2
  have hδ : ContinuousAt δ φ := by
    change ContinuousAt (fun ψ : CoeffPair p =>
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n -
       canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n)/2) φ
    exact (hR.sub hL).div_const 2
  have hδzero : δ φ = 0 := by
    have heq : δ φ = sourcePeriodicGapDisplacement hp hp1 φ n / 2 := by
      simp only [δ, sourceStandardRootHalfGap, sourcePeriodicGapDisplacement_apply]
    rw [heq,hgap]
    simp
  have ha : ContinuousAt a φ :=
    continuousAt_sourceCriticalDisplacement_of_realType hp hp1 φ hreal
  have hbase : ContinuousAt
      (fun ψ : CoeffPair p => (τ ψ,(a ψ,ψ))) φ :=
    hτ.prodMk (ha.prodMk continuousAt_id)
  have hphase (ψ : CoeffPair p) (z : ℂ) :
      I * sourceCriticalRootRatioExtension hp hp1 n ψ z =
        Q (z,(a ψ,ψ)) := by
    change I * (-I * Q (z,(a ψ,ψ))) = Q (z,(a ψ,ψ))
    calc
      I * (-I * Q (z,(a ψ,ψ))) = -(I^2) * Q (z,(a ψ,ψ)) := by ring
      _ = Q (z,(a ψ,ψ)) := by simp [Complex.I_sq]
  intro ε hε
  obtain ⟨ρ,hρ,hQball⟩ := Metric.continuousAt_iff.mp hQ ε hε
  have hbaseNear : ∀ᶠ ψ : CoeffPair p in 𝓝 φ,
      dist (τ ψ,(a ψ,ψ)) t < ρ/2 :=
    hbase.eventually (Metric.ball_mem_nhds _ (half_pos hρ))
  have hδNear : ∀ᶠ ψ : CoeffPair p in 𝓝 φ, ‖δ ψ‖ < ρ/2 := by
    have h := hδ.eventually (Metric.ball_mem_nhds _ (half_pos hρ))
    simpa only [hδzero, mem_ball, dist_zero_right] using h
  filter_upwards [hbaseNear,hδNear] with ψ hψbase hψδ θ
  rw [hphase ψ _,hphase φ _]
  let z := τ ψ + δ ψ * (Real.cos θ:ℂ)
  have hcos : ‖(Real.cos θ:ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using Real.abs_cos_le_one θ
  have hz : dist z (τ ψ) ≤ ‖δ ψ‖ := by
    simp only [z, dist_eq_norm, add_sub_cancel_left, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) hcos
  have hpath : dist (z,(a ψ,ψ)) t < ρ := by
    have htri := dist_triangle (z,(a ψ,ψ)) (τ ψ,(a ψ,ψ)) t
    have hstep : dist (z,(a ψ,ψ)) (τ ψ,(a ψ,ψ)) ≤ ‖δ ψ‖ := by
      simpa only [dist_prod_same_right] using hz
    linarith
  simpa only [dist_eq_norm] using hQball hpath

/-- The explicit collapsed value itself depends continuously on the
source at every collapsed real-type gap. -/
theorem continuousAt_sourceNormalizedActionCollapsedCandidate_of_realType_zeroGap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (hgap : sourcePeriodicGapDisplacement hp hp1 φ n = 0) :
    ContinuousAt (sourceNormalizedActionCollapsedCandidate hp hp1 n) φ := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hnear :=
    eventually_uniform_sourceCriticalRootRatioExtension_cosine_of_collapsedGap
      hp hp1 n φ hreal hgap (4*ε) (by positivity)
  filter_upwards [hnear] with ψ hψ
  have hpoint : ‖I * sourceCriticalRootRatioExtension hp hp1 n ψ
      (sourceStandardRootMidpoint hp hp1 ψ n) -
      I * sourceCriticalRootRatioExtension hp hp1 n φ
        (sourceStandardRootMidpoint hp hp1 φ n)‖ < 4*ε := by
    simpa only [Real.cos_pi_div_two, Complex.ofReal_zero, mul_zero,
      add_zero] using hψ (Real.pi/2)
  rw [dist_eq_norm]
  change ‖(I * sourceCriticalRootRatioExtension hp hp1 n ψ
      (sourceStandardRootMidpoint hp hp1 ψ n)) / 4 -
    (I * sourceCriticalRootRatioExtension hp hp1 n φ
      (sourceStandardRootMidpoint hp hp1 φ n)) / 4‖ < ε
  rw [← sub_div, norm_div]
  norm_num only [norm_ofNat]
  nlinarith

/-- The raw quotient has the claimed continuous limit along any
open real-type source family approaching a collapsed real-type gap.
The complex analytic extension through the full zero locus remains a
separate theorem. -/
theorem sourceRawNormalizedAction_tendsto_collapsedCandidate_of_openRealGaps
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (hgap : sourcePeriodicGapDisplacement hp hp1 φ n = 0)
    (F : Filter (CoeffPair p)) (hφ : Tendsto id F (𝓝 φ))
    (hopen : ∀ᶠ ψ in F,
      IsRealType (CoeffPair.toMax p ψ) ∧
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n).re <
        (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n).re) :
    Tendsto (sourceRawNormalizedAction hp hp1 n) F
      (𝓝 (sourceNormalizedActionCollapsedCandidate hp hp1 n φ)) := by
  let c := I * sourceCriticalRootRatioExtension hp hp1 n φ
    (sourceStandardRootMidpoint hp hp1 φ n)
  let r (ψ : CoeffPair p) :=
    ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ *
      ‖sourceCriticalGapQuotient hp hp1 ψ n‖
  have hr : Tendsto r F (𝓝 0) :=
    sourceCriticalNormalizedOffset_tendsto_zero_of_collapsedGap
      hp hp1 n φ hreal hgap F hφ
  have hfactor (δ : ℝ) (hδ : 0 < δ) : ∀ᶠ ψ in F, ∀ θ : ℝ,
      ‖I * sourceCriticalRootRatioExtension hp hp1 n ψ
        (sourceStandardRootMidpoint hp hp1 ψ n +
          sourceStandardRootHalfGap hp hp1 ψ n * (Real.cos θ:ℂ)) - c‖ ≤ δ := by
    have hnear := hφ.eventually
      (eventually_uniform_sourceCriticalRootRatioExtension_cosine_of_collapsedGap
        hp hp1 n φ hreal hgap δ hδ)
    filter_upwards [hnear] with ψ hψ θ
    exact (hψ θ).le
  have hfour : Tendsto (fun ψ : CoeffPair p =>
      4 * sourceRawNormalizedAction hp hp1 n ψ) F (𝓝 c) := by
    apply Metric.tendsto_nhds.mpr
    intro η hη
    let δ := η/4
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hcont : ContinuousAt (fun x : ℝ =>
        2 * (2*x+1)^2*δ + 8*x^2*‖c‖) 0 := by fun_prop
    have hlimit : Tendsto (fun ψ : CoeffPair p =>
        2 * (2*r ψ+1)^2*δ + 8*(r ψ)^2*‖c‖) F (𝓝 (2*δ)) := by
      change Tendsto ((fun x : ℝ =>
        2 * (2*x+1)^2*δ + 8*x^2*‖c‖) ∘ r) F (𝓝 (2*δ))
      simpa using hcont.tendsto.comp hr
    have hlt : 2*δ < η := by dsimp [δ]; linarith
    have hnear := hlimit.eventually (gt_mem_nhds hlt)
    filter_upwards [hopen,hfactor δ hδ,hnear] with ψ hψ hf hm
    rw [dist_eq_norm]
    have hb := norm_sourceRawNormalizedAction_sub_limitFactor_le
      hp hp1 ψ hψ.1 n hψ.2 c δ hf
    have hb' : ‖4 * sourceRawNormalizedAction hp hp1 n ψ - c‖ ≤
        2 * (2*r ψ+1)^2*δ + 8*(r ψ)^2*‖c‖ := by
      simpa only [r, mul_pow, mul_assoc] using hb
    exact hb'.trans_lt hm
  have hscaled := hfour.div_const (4:ℂ)
  have hfun : (fun ψ : CoeffPair p =>
      4 * sourceRawNormalizedAction hp hp1 n ψ / 4) =
        sourceRawNormalizedAction hp hp1 n := by
    funext ψ
    apply (div_eq_iff (by norm_num : (4:ℂ) ≠ 0)).2
    ring
  rw [hfun] at hscaled
  exact hscaled

/-- The explicit collapsed candidate is the limit of the raw quotient
within the open real-type gap locus. -/
theorem sourceRawNormalizedAction_tendsto_collapsedCandidate_within_openRealGaps
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (hgap : sourcePeriodicGapDisplacement hp hp1 φ n = 0) :
    Tendsto (sourceRawNormalizedAction hp hp1 n)
      (𝓝[{ψ : CoeffPair p |
        IsRealType (CoeffPair.toMax p ψ) ∧
          (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
            (periodOnePotential_mem ψ) n).re <
          (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
            (periodOnePotential_mem ψ) n).re}] φ)
      (𝓝 (sourceNormalizedActionCollapsedCandidate hp hp1 n φ)) := by
  let S : Set (CoeffPair p) := {ψ |
    IsRealType (CoeffPair.toMax p ψ) ∧
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re}
  change Tendsto (sourceRawNormalizedAction hp hp1 n) (𝓝[S] φ)
    (𝓝 (sourceNormalizedActionCollapsedCandidate hp hp1 n φ))
  have hφ : Tendsto id (𝓝[S] φ) (𝓝 φ) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  exact sourceRawNormalizedAction_tendsto_collapsedCandidate_of_openRealGaps
    hp hp1 n φ hreal hgap _ hφ self_mem_nhdsWithin

/-- The normalized action on real-type sources, filled in at a
collapsed gap by the cosine-moment value. -/
def sourceNormalizedActionRealExtension
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (ψ : CoeffPair p) : ℂ := by
  classical
  exact if sourcePeriodicGapDisplacement hp hp1 ψ n = 0 then
    sourceNormalizedActionCollapsedCandidate hp hp1 n ψ
  else sourceRawNormalizedAction hp hp1 n ψ

/-- This explicit real-type extension is continuous at every
collapsed real-type source, relative to the real-type locus. -/
theorem continuousWithinAt_sourceNormalizedActionRealExtension_of_zeroGap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (hgap : sourcePeriodicGapDisplacement hp hp1 φ n = 0) :
    ContinuousWithinAt (sourceNormalizedActionRealExtension hp hp1 n)
      (realTypeSourceLocus p) φ := by
  let S : Set (CoeffPair p) := {ψ |
    IsRealType (CoeffPair.toMax p ψ) ∧
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re}
  have hraw : Tendsto (sourceRawNormalizedAction hp hp1 n) (𝓝[S] φ)
      (𝓝 (sourceNormalizedActionCollapsedCandidate hp hp1 n φ)) :=
    sourceRawNormalizedAction_tendsto_collapsedCandidate_within_openRealGaps
      hp hp1 n φ hreal hgap
  have hcand : ContinuousAt
      (sourceNormalizedActionCollapsedCandidate hp hp1 n) φ :=
    continuousAt_sourceNormalizedActionCollapsedCandidate_of_realType_zeroGap
      hp hp1 n φ hreal hgap
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hrawNear : ∀ᶠ ψ : CoeffPair p in 𝓝 φ,
      ψ ∈ S → dist (sourceRawNormalizedAction hp hp1 n ψ)
        (sourceNormalizedActionCollapsedCandidate hp hp1 n φ) < ε :=
    eventually_nhdsWithin_iff.mp
      (hraw.eventually (Metric.ball_mem_nhds _ hε))
  have hcandNear : ∀ᶠ ψ : CoeffPair p in 𝓝 φ,
      dist (sourceNormalizedActionCollapsedCandidate hp hp1 n ψ)
        (sourceNormalizedActionCollapsedCandidate hp hp1 n φ) < ε :=
    hcand.eventually (Metric.ball_mem_nhds _ hε)
  apply eventually_nhdsWithin_iff.mpr
  filter_upwards [hrawNear,hcandNear] with ψ hψraw hψcand hψreal
  have hψreal' : IsRealType (CoeffPair.toMax p ψ) := hψreal
  by_cases hψgap : sourcePeriodicGapDisplacement hp hp1 ψ n = 0
  · simpa only [sourceNormalizedActionRealExtension,
      if_pos hψgap, if_pos hgap] using hψcand
  · have hψopen := source_openRealGap_of_realType_gap_ne_zero
      hp hp1 n ψ hψreal' hψgap
    have hψS : ψ ∈ S := ⟨hψreal',hψopen⟩
    simpa only [sourceNormalizedActionRealExtension,
      if_neg hψgap, if_pos hgap] using hψraw hψS

/-- Away from a collapsed gap, the piecewise real-type extension
agrees locally with the complex differentiable raw quotient. -/
theorem continuousAt_sourceNormalizedActionRealExtension_of_nonzeroGap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (hgap : sourcePeriodicGapDisplacement hp hp1 φ n ≠ 0) :
    ContinuousAt (sourceNormalizedActionRealExtension hp hp1 n) φ := by
  have hL := continuousAt_canonicalPeriodicLeft_periodOne_of_realType
    hp hp1 φ hreal n
  have hR := continuousAt_canonicalPeriodicRight_periodOne_of_realType
    hp hp1 φ hreal n
  have hγ : ContinuousAt (fun ψ : CoeffPair p =>
      sourcePeriodicGapDisplacement hp hp1 ψ n) φ := by
    simp only [sourcePeriodicGapDisplacement_apply, canonicalPeriodicGap]
    exact hR.sub hL
  have hnear : ∀ᶠ ψ : CoeffPair p in 𝓝 φ,
      sourcePeriodicGapDisplacement hp hp1 ψ n ≠ 0 :=
    hγ.eventually_ne hgap
  have heq : ∀ᶠ ψ : CoeffPair p in 𝓝 φ,
      sourceNormalizedActionRealExtension hp hp1 n ψ =
        sourceRawNormalizedAction hp hp1 n ψ := by
    filter_upwards [hnear] with ψ hψ
    simp only [sourceNormalizedActionRealExtension, if_neg hψ]
  exact (differentiableAt_sourceRawNormalizedAction_of_gap_ne_zero
    hp hp1 n φ hreal hgap).continuousAt.congr_of_eventuallyEq heq

/-- The normalized action with its cosine-moment value filled in is
continuous on the full real-type source locus, at open and collapsed
gaps alike. -/
theorem continuousWithinAt_sourceNormalizedActionRealExtension_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ContinuousWithinAt (sourceNormalizedActionRealExtension hp hp1 n)
      (realTypeSourceLocus p) φ := by
  by_cases hgap : sourcePeriodicGapDisplacement hp hp1 φ n = 0
  · exact continuousWithinAt_sourceNormalizedActionRealExtension_of_zeroGap
      hp hp1 n φ hreal hgap
  · exact (continuousAt_sourceNormalizedActionRealExtension_of_nonzeroGap
      hp hp1 n φ hreal hgap).continuousWithinAt

end NLS.ZakharovShabat
