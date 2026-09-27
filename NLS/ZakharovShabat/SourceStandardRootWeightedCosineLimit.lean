import NLS.ZakharovShabat.SourceStandardRootWeightedTransverseBound
import NLS.ZakharovShabat.SourceCriticalRootRatioVerticalLimits
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# One-sided limits of weighted standard-root cosine integrals

The cosine Jacobian cancels the selected root's inverse-square-root
endpoint singularity. The resulting uniformly bounded integrands
converge to the upper or lower gap-side boundary value.
-/

noncomputable section
open Set Metric Filter Topology Complex MeasureTheory intervalIntegral
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The selected-root quotient pulled back to a vertically displaced
cosine parametrization of the real gap. -/
def sourceStandardRoot_weighted_cosineIntegral
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (g : ℂ → ℂ) (y : ℝ) : ℂ :=
  ∫ θ in (0:ℝ)..Real.pi,
    let z := sourceCanonicalRootGapPoint hp hp1 ψ n (Real.cos θ) + (y:ℂ)*I
    (g z / sourceStandardRoot hp hp1 ψ n z) *
      (sourceStandardRootHalfGap hp hp1 ψ n * (Real.sin θ:ℂ))

/-- The corresponding cosine-parametrized upper or lower boundary
integral, with endpoint values understood in the Lebesgue sense. -/
def sourceStandardRoot_weighted_cosineBoundaryIntegral
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (g : ℂ → ℂ) (upper : Bool) : ℂ :=
  ∫ θ in (0:ℝ)..Real.pi,
    let t := Real.cos θ
    let z := sourceCanonicalRootGapPoint hp hp1 ψ n t
    (g z / ((if upper then -sourceStandardRootHalfGap hp hp1 ψ n * I
      else sourceStandardRootHalfGap hp hp1 ψ n * I) *
        (Real.sqrt (1-t^2):ℂ))) *
      (sourceStandardRootHalfGap hp hp1 ψ n * (Real.sin θ:ℂ))

/-- Positive and negative vertical displacements converge to the
corresponding weighted standard-root boundary integrals. -/
theorem sourceStandardRoot_weighted_cosineIntegral_tendsto_boundary
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (g : ℂ → ℂ) (U : Set ℂ) (hUopen : IsOpen U)
    (hgapU : standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ n)
      (sourceStandardRootHalfGap hp hp1 ψ n) ⊆ U)
    (hg : AnalyticOnNhd ℂ g U) (upper : Bool) :
    Tendsto (sourceStandardRoot_weighted_cosineIntegral hp hp1 ψ n g)
      (if upper then 𝓝[Set.Ioi 0] (0:ℝ) else 𝓝[Set.Iio 0] (0:ℝ))
      (𝓝 (sourceStandardRoot_weighted_cosineBoundaryIntegral
        hp hp1 ψ n g upper)) := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let δ := sourceStandardRootHalfGap hp hp1 ψ n
  let d : ℝ := ((canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re -
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)/2
  let L : Filter ℝ := if upper then 𝓝[Set.Ioi 0] (0:ℝ)
    else 𝓝[Set.Iio 0] (0:ℝ)
  letI : L.IsCountablyGenerated := by
    cases upper <;> dsimp [L] <;> infer_instance
  have hδ : δ = (d:ℂ) :=
    sourceStandardRootHalfGap_eq_ofReal_affineJacobian hp hp1 ψ hreal n
  have hδne : δ ≠ 0 :=
    sourceStandardRootHalfGap_ne_zero_of_openRealGap hp hp1 ψ hreal n hopen
  have hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n ≠ 0 :=
    sourceCanonicalPeriodicGap_ne_zero_of_openRealGap hp hp1 ψ hreal n hopen
  obtain ⟨ε,M,hε,_,hthick,hbound⟩ :=
    exists_sourceStandardRoot_weighted_transverse_bound
      hp hp1 ψ hreal n hopen g U hUopen hgapU hg
  let S := standardRootGapSegment τ δ
  have hside : ∀ᶠ y in L, y ≠ 0 ∧ |y| ≤ ε := by
    cases upper with
    | true =>
        dsimp [L]
        have hsmall0 : ∀ᶠ y in 𝓝 (0:ℝ), y < ε := Iio_mem_nhds hε
        have hsmall : ∀ᶠ y in 𝓝[Set.Ioi 0] (0:ℝ), y < ε :=
          hsmall0.filter_mono nhdsWithin_le_nhds
        filter_upwards [self_mem_nhdsWithin,hsmall] with y hy hyε
        exact ⟨hy.ne', by rw [abs_of_pos hy]; exact hyε.le⟩
    | false =>
        dsimp [L]
        have hsmall0 : ∀ᶠ y in 𝓝 (0:ℝ), -ε < y :=
          Ioi_mem_nhds (neg_lt_zero.mpr hε)
        have hsmall : ∀ᶠ y in 𝓝[Set.Iio 0] (0:ℝ), -ε < y :=
          hsmall0.filter_mono nhdsWithin_le_nhds
        filter_upwards [self_mem_nhdsWithin,hsmall] with y hy hyε
        exact ⟨hy.ne, by rw [abs_of_neg hy]; linarith⟩
  have hvertical (t y : ℝ) (ht : t ∈ Icc (-1:ℝ) 1)
      (hyε : |y| ≤ ε) :
      sourceCanonicalRootGapPoint hp hp1 ψ n t + (y:ℂ)*I ∈ U := by
    let q := sourceCanonicalRootGapPoint hp hp1 ψ n t
    let z := q+(y:ℂ)*I
    have hqS : q ∈ S := ⟨t,ht,rfl⟩
    have hdist : dist z q = |y| := by
      calc
        dist z q = ‖(y:ℂ)*I‖ := by
          rw [dist_eq_norm]
          congr 1
          dsimp [z]
          ring
        _ = |y| := by simp
    exact hthick (Metric.mem_cthickening_of_dist_le z q ε S hqS
      (by simpa [hdist] using hyε))
  have hweight : Continuous (fun θ : ℝ => δ * (Real.sin θ:ℂ)) := by
    fun_prop
  change Tendsto (fun y : ℝ => ∫ θ in (0:ℝ)..Real.pi,
      let z := sourceCanonicalRootGapPoint hp hp1 ψ n (Real.cos θ) + (y:ℂ)*I
      (g z / sourceStandardRoot hp hp1 ψ n z) * (δ*(Real.sin θ:ℂ))) L
    (𝓝 (∫ θ in (0:ℝ)..Real.pi,
      let t := Real.cos θ
      let z := sourceCanonicalRootGapPoint hp hp1 ψ n t
      (g z / ((if upper then -δ*I else δ*I) *
        (Real.sqrt (1-t^2):ℂ))) * (δ*(Real.sin θ:ℂ))))
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (bound := fun _ : ℝ => M)
  · filter_upwards [hside] with y hy
    have hpath : Continuous (fun θ : ℝ =>
        sourceCanonicalRootGapPoint hp hp1 ψ n (Real.cos θ) + (y:ℂ)*I) := by
      unfold sourceCanonicalRootGapPoint
      fun_prop
    have hQ : Continuous (fun θ : ℝ =>
        let z := sourceCanonicalRootGapPoint hp hp1 ψ n (Real.cos θ) + (y:ℂ)*I
        g z / sourceStandardRoot hp hp1 ψ n z) := by
      rw [continuous_iff_continuousAt]
      intro θ
      let z := sourceCanonicalRootGapPoint hp hp1 ψ n (Real.cos θ) + (y:ℂ)*I
      have hcos : Real.cos θ ∈ Icc (-1:ℝ) 1 := Real.cos_mem_Icc θ
      have hzU : z ∈ U := hvertical _ y hcos hy.2
      have hzdom : z ∈ sourceCanonicalRootDomain hp hp1 ψ :=
        sourceCanonicalRootGapPoint_vertical_mem_domain_of_realType
          hp hp1 ψ hreal n (Real.cos θ) y hy.1
      have hqa := ((hg z hzU).div
        (sourceStandardRoot_analyticAt hp hp1 ψ n z (hzdom n))
        (sourceStandardRoot_ne_zero_off_segment hp hp1 ψ n z (hzdom n)))
      have hcomp : ContinuousAt
          ((fun z : ℂ => g z / sourceStandardRoot hp hp1 ψ n z) ∘
            (fun θ : ℝ => sourceCanonicalRootGapPoint hp hp1 ψ n
              (Real.cos θ) + (y:ℂ)*I)) θ :=
        ContinuousAt.comp
          (f := fun θ : ℝ => sourceCanonicalRootGapPoint hp hp1 ψ n
            (Real.cos θ) + (y:ℂ)*I)
          (g := fun z : ℂ => g z / sourceStandardRoot hp hp1 ψ n z)
          hqa.continuousAt (hpath.continuousAt (x := θ))
      simpa only [Function.comp_def] using hcomp
    exact (hQ.mul hweight).aestronglyMeasurable
  · filter_upwards [hside] with y hy
    refine Filter.Eventually.of_forall ?_
    intro θ hθ
    have hθoc : θ ∈ Ioc 0 Real.pi := by
      simpa [uIoc_of_le (le_of_lt Real.pi_pos)] using hθ
    have hθcc : θ ∈ Icc 0 Real.pi := ⟨hθoc.1.le,hθoc.2⟩
    have hcos : Real.cos θ ∈ Icc (-1:ℝ) 1 := Real.cos_mem_Icc θ
    have hjac : δ*(Real.sin θ:ℂ) =
        ((d*Real.sqrt (1-Real.cos θ^2):ℝ):ℂ) := by
      rw [hδ,Real.sin_eq_sqrt_one_sub_cos_sq hθcc.1 hθcc.2]
      norm_cast
    rw [hjac]
    exact hbound (Real.cos θ) hcos y hy.1 hy.2
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall ?_
    intro θ hθ
    have hθoc : θ ∈ Ioc (0:ℝ) Real.pi := by
      simpa [uIoc_of_le (le_of_lt Real.pi_pos)] using hθ
    by_cases hπ : θ = Real.pi
    · subst θ
      simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0:ℂ)) L (𝓝 0))
    · have hθint : θ ∈ Ioo 0 Real.pi :=
        ⟨hθoc.1,lt_of_le_of_ne hθoc.2 hπ⟩
      let t := Real.cos θ
      let z₀ := sourceCanonicalRootGapPoint hp hp1 ψ n t
      have ht : t ∈ Ioo (-1:ℝ) 1 := cos_mem_gapInterior hθint
      have hz₀U : z₀ ∈ U := hgapU ⟨t,⟨ht.1.le,ht.2.le⟩,rfl⟩
      have hpath : Tendsto (fun y : ℝ => z₀+(y:ℂ)*I) L (𝓝 z₀) := by
        have hc : ContinuousAt (fun y : ℝ => z₀+(y:ℂ)*I) 0 := by
          fun_prop
        have hmono : L ≤ 𝓝 (0:ℝ) := by
          cases upper <;> exact nhdsWithin_le_nhds
        simpa using hc.tendsto.mono_left hmono
      have hnum : Tendsto (fun y : ℝ => g (z₀+(y:ℂ)*I))
          L (𝓝 (g z₀)) := (hg z₀ hz₀U).continuousAt.tendsto.comp hpath
      have hroot : Tendsto (fun y : ℝ =>
          sourceStandardRoot hp hp1 ψ n (z₀+(y:ℂ)*I)) L
          (𝓝 ((if upper then -δ*I else δ*I) *
            (Real.sqrt (1-t^2):ℂ))) := by
        cases upper with
        | true =>
            exact (sourceStandardRoot_tendsto_gap_upper_side
              hp hp1 ψ n t hgap ht.1.le ht.2.le).comp
              (sourceCanonicalRootGapPoint_vertical_tendsto_upperSide
                hp hp1 ψ hreal n hopen t)
        | false =>
            exact (sourceStandardRoot_tendsto_gap_lower_side
              hp hp1 ψ n t hgap ht.1.le ht.2.le).comp
              (sourceCanonicalRootGapPoint_vertical_tendsto_lowerSide
                hp hp1 ψ hreal n hopen t)
      have hden : ((if upper then -δ*I else δ*I) *
          (Real.sqrt (1-t^2):ℂ)) ≠ 0 := by
        have hs : Real.sqrt (1-t^2) = Real.sin θ := by
          exact Real.sin_eq_sqrt_one_sub_cos_sq hθint.1.le hθint.2.le |>.symm
        have hsin : (Real.sin θ:ℂ) ≠ 0 := by
          exact_mod_cast (Real.sin_pos_of_pos_of_lt_pi hθint.1 hθint.2).ne'
        rw [hs]
        have hfac : (if upper then -δ*I else δ*I) ≠ 0 := by
          cases upper <;> simp [hδne]
        exact mul_ne_zero hfac hsin
      exact (hnum.div hroot hden).mul tendsto_const_nhds

/-- The cosine boundary value is the previously defined gap-side
boundary integral from Lemma 10.4. -/
theorem sourceStandardRoot_weighted_cosineBoundaryIntegral_eq_gapSide
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (g : ℂ → ℂ) (upper : Bool) :
    sourceStandardRoot_weighted_cosineBoundaryIntegral
      hp hp1 ψ n g upper =
      gapSideBoundaryIntegral
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n) g 1 upper := by
  unfold sourceStandardRoot_weighted_cosineBoundaryIntegral
    gapSideBoundaryIntegral
  rw [Real.arccos_one]
  apply intervalIntegral.integral_congr
  intro θ _
  change (g (sourceStandardRootMidpoint hp hp1 ψ n +
      sourceStandardRootHalfGap hp hp1 ψ n * (Real.cos θ:ℂ)) /
      ((if upper then -sourceStandardRootHalfGap hp hp1 ψ n * I
        else sourceStandardRootHalfGap hp hp1 ψ n * I) *
        (Real.sqrt (1-(Real.cos θ)^2):ℂ))) *
      (sourceStandardRootHalfGap hp hp1 ψ n * (Real.sin θ:ℂ)) = _
  simp only [div_eq_mul_inv]
  ring

end NLS.ZakharovShabat
