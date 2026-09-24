import NLS.ZakharovShabat.SourceActionOuterArcLimit
import NLS.ZakharovShabat.SourceCriticalRootRatioCosineIntegralLimit

/-!
# Weighted cosine integrals approaching the two real gap sides

The quotient's transverse cosine bound remains integrable after
multiplication by the bounded affine action weight. Dominated
convergence then identifies both one-sided horizontal limits with
their canonical-root boundary integrals.
-/

noncomputable section
open Set Filter Topology Complex MeasureTheory intervalIntegral
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The recentered action integrand along a vertically displaced
cosine-parametrized gap. -/
def sourceAction_cosineIntegral
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (q : ℂ) (y : ℝ) : ℂ :=
  ∫ θ in (0:ℝ)..Real.pi,
    let z := sourceCanonicalRootGapPoint hp hp1 ψ n (Real.cos θ) + (y:ℂ)*I
    ((z-q) * sourceCriticalRootRatioJoint hp hp1 (z,ψ)) *
      (sourceStandardRootHalfGap hp hp1 ψ n * (Real.sin θ:ℂ))

/-- The corresponding upper or lower canonical-root boundary integral. -/
def sourceAction_cosineBoundaryIntegral
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (q : ℂ) (upper : Bool) : ℂ :=
  ∫ θ in (0:ℝ)..Real.pi,
    let t := Real.cos θ
    let z := sourceCanonicalRootGapPoint hp hp1 ψ n t
    ((z-q) *
      (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
        (if upper then sourceCanonicalRootGapUpperValue hp hp1 ψ n t
          else sourceCanonicalRootGapLowerValue hp hp1 ψ n t))) *
      (sourceStandardRootHalfGap hp hp1 ψ n * (Real.sin θ:ℂ))

/-- Positive and negative vertical displacements converge to the
weighted upper and lower cosine boundary integrals, respectively. -/
theorem sourceAction_cosineIntegral_tendsto_boundary
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (q : ℂ) (upper : Bool) :
    Tendsto (sourceAction_cosineIntegral hp hp1 ψ n q)
      (if upper then 𝓝[Set.Ioi 0] (0:ℝ) else 𝓝[Set.Iio 0] (0:ℝ))
      (𝓝 (sourceAction_cosineBoundaryIntegral hp hp1 ψ n q upper)) := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let δ := sourceStandardRootHalfGap hp hp1 ψ n
  let d : ℝ := ((canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re -
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)/2
  let Q : ℂ → ℂ := fun z => sourceCriticalRootRatioJoint hp hp1 (z,ψ)
  let L : Filter ℝ := if upper then 𝓝[Set.Ioi 0] (0:ℝ)
    else 𝓝[Set.Iio 0] (0:ℝ)
  letI : L.IsCountablyGenerated := by
    cases upper <;> dsimp [L] <;> infer_instance
  have hδ : δ = (d:ℂ) :=
    sourceStandardRootHalfGap_eq_ofReal_affineJacobian hp hp1 ψ hreal n
  obtain ⟨ε,M,hε,hM,hbound⟩ :=
    exists_sourceCriticalRootRatio_transverse_weighted_bound
      hp hp1 ψ hreal n hopen
  let B := ‖τ-q‖+‖δ‖+ε+1
  have hB : 0 < B := by dsimp [B]; positivity
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
  have hweight : Continuous (fun θ : ℝ => δ * (Real.sin θ:ℂ)) := by
    fun_prop
  change Tendsto (fun y : ℝ => ∫ θ in (0:ℝ)..Real.pi,
      let z := sourceCanonicalRootGapPoint hp hp1 ψ n (Real.cos θ) + (y:ℂ)*I
      ((z-q)*Q z)*(δ*(Real.sin θ:ℂ))) L
    (𝓝 (∫ θ in (0:ℝ)..Real.pi,
      let t := Real.cos θ
      let z := sourceCanonicalRootGapPoint hp hp1 ψ n t
      ((z-q) * (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
        (if upper then sourceCanonicalRootGapUpperValue hp hp1 ψ n t
          else sourceCanonicalRootGapLowerValue hp hp1 ψ n t))) *
        (δ*(Real.sin θ:ℂ))))
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (bound := fun _ : ℝ => B*M)
  · filter_upwards [hside] with y hy
    have hpath : Continuous (fun θ : ℝ =>
        sourceCanonicalRootGapPoint hp hp1 ψ n (Real.cos θ) + (y:ℂ)*I) := by
      unfold sourceCanonicalRootGapPoint
      fun_prop
    have hQ : Continuous (fun θ : ℝ =>
        Q (sourceCanonicalRootGapPoint hp hp1 ψ n (Real.cos θ) + (y:ℂ)*I)) :=
      (sourceCriticalRootRatio_vertical_continuous
        hp hp1 ψ hreal n y hy.1).comp Real.continuous_cos
    exact (((hpath.sub continuous_const).mul hQ).mul
      hweight).aestronglyMeasurable
  · filter_upwards [hside] with y hy
    refine Filter.Eventually.of_forall ?_
    intro θ hθ
    have hθoc : θ ∈ Ioc 0 Real.pi := by
      simpa [uIoc_of_le (le_of_lt Real.pi_pos)] using hθ
    have hθcc : θ ∈ Icc 0 Real.pi := ⟨hθoc.1.le,hθoc.2⟩
    have hcos : Real.cos θ ∈ Icc (-1:ℝ) 1 := Real.cos_mem_Icc θ
    have hcosNorm : ‖(Real.cos θ:ℂ)‖ ≤ 1 := by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using
        (abs_le.mpr hcos)
    let z := sourceCanonicalRootGapPoint hp hp1 ψ n (Real.cos θ) + (y:ℂ)*I
    have hcoord : ‖δ*(Real.cos θ:ℂ)‖ ≤ ‖δ‖ := by
      calc
        _ = ‖δ‖*‖(Real.cos θ:ℂ)‖ := norm_mul _ _
        _ ≤ ‖δ‖*1 := mul_le_mul_of_nonneg_left hcosNorm (norm_nonneg _)
        _ = ‖δ‖ := mul_one _
    have hweightBound : ‖z-q‖ ≤ B := by
      have hz : z-q = (τ-q)+δ*(Real.cos θ:ℂ)+(y:ℂ)*I := by
        dsimp [z,sourceCanonicalRootGapPoint,τ,δ]
        ring
      rw [hz]
      have hiy : ‖(y:ℂ)*I‖ = |y| := by simp
      calc
        _ ≤ ‖(τ-q)+δ*(Real.cos θ:ℂ)‖+‖(y:ℂ)*I‖ := norm_add_le _ _
        _ ≤ (‖τ-q‖+‖δ*(Real.cos θ:ℂ)‖)+‖(y:ℂ)*I‖ := by
          gcongr
          exact norm_add_le _ _
        _ ≤ B := by dsimp [B]; rw [hiy]; linarith [hcoord,hy.2]
    have hjac : δ*(Real.sin θ:ℂ) =
        ((d*Real.sqrt (1-Real.cos θ^2):ℝ):ℂ) := by
      rw [hδ, Real.sin_eq_sqrt_one_sub_cos_sq hθcc.1 hθcc.2]
      norm_cast
    have hQbound : ‖Q z * (δ*(Real.sin θ:ℂ))‖ ≤ M := by
      rw [hjac]
      exact hbound (Real.cos θ) hcos y hy.1 hy.2
    change ‖((z-q)*Q z)*(δ*(Real.sin θ:ℂ))‖ ≤ B*M
    calc
      _ = ‖z-q‖*‖Q z*(δ*(Real.sin θ:ℂ))‖ := by
        rw [mul_assoc,norm_mul]
      _ ≤ B*‖Q z*(δ*(Real.sin θ:ℂ))‖ :=
        mul_le_mul_of_nonneg_right hweightBound (norm_nonneg _)
      _ ≤ B*M := mul_le_mul_of_nonneg_left hQbound hB.le
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
      let z₀ := sourceCanonicalRootGapPoint hp hp1 ψ n (Real.cos θ)
      have hpath : Tendsto (fun y : ℝ => z₀+(y:ℂ)*I-q) L
          (𝓝 (z₀-q)) := by
        have hc : ContinuousAt (fun y : ℝ => z₀+(y:ℂ)*I-q) 0 := by
          fun_prop
        have hmono : L ≤ 𝓝 (0:ℝ) := by
          cases upper <;> exact nhdsWithin_le_nhds
        simpa using hc.tendsto.mono_left hmono
      have hquot : Tendsto (fun y : ℝ => Q (z₀+(y:ℂ)*I)) L
          (𝓝 (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z₀ /
            (if upper then
              sourceCanonicalRootGapUpperValue hp hp1 ψ n (Real.cos θ)
            else sourceCanonicalRootGapLowerValue hp hp1 ψ n (Real.cos θ)))) := by
        cases upper with
        | true =>
            exact sourceCriticalRootRatio_tendsto_vertical_upper
              hp hp1 ψ hreal n hopen (Real.cos θ)
                (cos_mem_gapInterior hθint)
        | false =>
            exact sourceCriticalRootRatio_tendsto_vertical_lower
              hp hp1 ψ hreal n hopen (Real.cos θ)
                (cos_mem_gapInterior hθint)
      exact (hpath.mul hquot).mul tendsto_const_nhds

end NLS.ZakharovShabat
