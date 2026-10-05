import NLS.ComplexAnalysis.ParametricSineSquareMean
import NLS.ZakharovShabat.SourceMomentFreeFactors
import NLS.ZakharovShabat.SourceAbelianMomentErrorDomain
import NLS.ZakharovShabat.SourceAbelianMomentEvenNumeratorJoint
import NLS.ZakharovShabat.SourcePeriodicMidpointGapContinuity

/-! # Regular second moments at the zero potential

Extract the squared gap before integration. The remaining weighted mean
is continuous at zero and has the diagonal value pi/4.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

namespace SourceFullAbelianUniformCauchyFamily

/-- The second-moment coefficient after extracting the squared gap,
defined by a regular integral even when that gap is collapsed. -/
def normalizedSecondMoment (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (n k : ℤ) (ψ : CoeffPair p) : ℂ :=
  (Complex.I/2) * parametricSineSquareMean
    (fun t : ℂ × CoeffPair p =>
      (sourceFullAbelianCauchyQuotient hp hp1 W k (C.discs.center k) (C.discs.outer k) t)^2 *
        sourceMomentRegularNumerator hp hp1 n k (s n t.2 : Coeff p) t.2 t.1)
    (fun χ => sourceStandardRootMidpoint hp hp1 χ k)
    (sourceStandardRootHalfGap hp hp1 ψ k,ψ)

/-- The exact squared-gap factorization of the actual second moment,
with no nonzero-gap assumption and no compatibility of ambient domains required. -/
theorem moment_two_eq_squaredGap_mul_normalized
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    {V : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (A : SourceAbelianMomentAtlas hp hp1 V s) (D : SourceAbelianMomentErrorDomain A)
    (ψ : CoeffPair p) (hψ : ψ ∈ D.domain)
    (hC : ψ ∈ ball C.discs.source.val C.discs.sourceRadius) (n k : ℤ) :
    A.moment n k 2 ψ = (sourcePeriodicGapDisplacement hp hp1 ψ k)^2 *
      C.normalizedSecondMoment s n k ψ := by
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp (D.source_subset hψ)
  obtain ⟨E₀⟩ := (A.localChart φ).charts ψ hφ
  obtain ⟨E₁⟩ := C.charts ψ hC
  let Q := sourceFullAbelianCauchyQuotient hp hp1 W k (C.discs.center k) (C.discs.outer k)
  let R := sourceMomentRegularNumerator hp hp1 n k (s n ψ : Coeff p) ψ
  let τ := sourceStandardRootMidpoint hp hp1 ψ k
  let δ := sourceStandardRootHalfGap hp hp1 ψ k
  have he (θ : ℝ) :
      sourceAbelianMomentEvenNumerator hp hp1 V n k 1 (s n ψ : Coeff p) ψ (τ+δ*(Real.cos θ:ℂ)) =
        -((sourcePeriodicGapDisplacement hp hp1 ψ k)^2/4) *
          ((Real.sin θ:ℂ)^2 * (Q (τ+δ*(Real.cos θ:ℂ),ψ)^2 * R (τ+δ*(Real.cos θ:ℂ)))) := by
    have hz : τ+δ*(Real.cos θ:ℂ) ∈ sourcePeriodicSegment hp hp1 ψ k := by
      rw [sourcePeriodicSegment_eq_midpoint_segment]
      simpa only [cosineGapPoint,← Complex.ofReal_cos] using cosineGapPoint_real_mem_segment τ δ θ
    have hsq := C.fullSquare_eq_square k ψ hC (C.segment_subset_outer k ψ hC hz)
    change sourceFullAbelianSquare hp hp1 W k (τ+δ*(Real.cos θ:ℂ),ψ) =
      sourceAngularSelectedPolynomial hp hp1 ψ k (τ+δ*(Real.cos θ:ℂ)) *
        Q (τ+δ*(Real.cos θ:ℂ),ψ)^2 at hsq
    rw [sourceAbelianMomentEvenNumerator,pow_one,
      sourceFullAbelianSquare_independent_neighborhood E₀ E₁,
      hsq,
      ← sourceStandardRootGapBoundary_sq hp hp1 ψ k θ true]
    simp only [sourceStandardRootGapBoundary,↓reduceIte]
    dsimp only [Q,R,δ,sourceStandardRootHalfGap]
    rw [sourcePeriodicGapDisplacement_apply]
    ring_nf
    simp
    ring
  rw [D.cosine_formula ψ hψ n k]
  unfold sourceGapCosineMean parametricCosineMean normalizedSecondMoment parametricSineSquareMean
  change -(2*Complex.I)*(∫ θ in (0:ℝ)..Real.pi,
    sourceAbelianMomentEvenNumerator hp hp1 V n k 1 (s n ψ : Coeff p) ψ (τ+δ*(Real.cos θ:ℂ))) = _
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul]
  dsimp only [Q,R,τ,δ]
  ring

/-- The regular coefficient has the exact free diagonal value. -/
theorem normalizedSecondMoment_zero
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (hC : (0 : CoeffPair p) ∈ ball C.discs.source.val C.discs.sourceRadius)
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n} (hs : ∀ n, s n 0 = 0) (n k : ℤ) :
    C.normalizedSecondMoment s n k 0 = if k = n then (Real.pi : ℂ)/4 else 0 := by
  have hδ : sourceStandardRootHalfGap hp hp1 (0 : CoeffPair p) k = 0 := by
    unfold sourceStandardRootHalfGap
    rw [show canonicalPeriodicGap hp hp1 (periodOnePotential (0 : CoeffPair p))
      (periodOnePotential_mem 0) k = 0 from by simpa only [map_zero] using canonicalPeriodicGap_zero hp hp1 k]
    exact zero_div 2
  have hτ : sourceStandardRootMidpoint hp hp1 (0 : CoeffPair p) k = (Real.pi : ℂ)*k := by
    simpa only [sourceStandardRootMidpoint,map_zero] using canonicalPeriodicMidpoint_zero hp hp1 k
  have hz : (Real.pi : ℂ)*k ∈ ball (C.discs.center k) (C.discs.outer k) := by
    apply C.segment_subset_outer k 0 hC
    simp [sourcePeriodicSegment_zero_source]
  rw [normalizedSecondMoment,hδ,parametricSineSquareMean_zero,hτ,
    C.quotient_zero_source hC k _ hz,hs]
  change Complex.I/2 * ((Real.pi:ℂ)/2 * (Complex.I^2 *
    sourceMomentRegularNumerator hp hp1 n k (0 : Coeff p) 0 ((Real.pi:ℂ)*k))) = _
  rw [sourceMomentRegularNumerator_zero_freeCenter]
  split_ifs
  · ring_nf
    simp
  · simp

/-- The regular second-moment coefficient is continuous at the free source.
Only the chosen numerator branch and existing joint analytic factors enter. -/
theorem continuousAt_normalizedSecondMoment_zero
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (hC : (0 : CoeffPair p) ∈ ball C.discs.source.val C.discs.sourceRadius)
    {V : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (hs : SourcePsiIsolatingComplexExtension hp hp1 V s) (hV : (0 : CoeffPair p) ∈ V)
    (n k : ℤ) : ContinuousAt (C.normalizedSecondMoment s n k) 0 := by
  let τ := fun ψ : CoeffPair p => sourceStandardRootMidpoint hp hp1 ψ k
  let δ := fun ψ : CoeffPair p => sourceStandardRootHalfGap hp hp1 ψ k
  let g : ℂ × CoeffPair p → ℂ := fun t =>
    (sourceFullAbelianCauchyQuotient hp hp1 W k (C.discs.center k) (C.discs.outer k) t)^2 *
      sourceMomentRegularNumerator hp hp1 n k (s n t.2 : Coeff p) t.2 t.1
  have hreal : IsRealType (CoeffPair.toMax p (0 : CoeffPair p)) :=
    (0 : realTypeSourceSubmodule p).property
  have hz : τ 0 ∈ ball (C.discs.center k) (C.discs.outer k) :=
    C.segment_subset_outer k 0 hC (sourcePeriodicMidpoint_mem_segment hp hp1 0 k)
  have hdom : τ 0 ∈ sourceStandardRootOmittedDomain hp hp1 0 k :=
    C.discs.avoids_other 0 hC k (ball_subset_closedBall hz)
  obtain ⟨U,_,_,hrealU,hO⟩ := exists_global_source_analytic_omittedJointProduct hp hp1
  have hprod := (hO k).2.1 (τ 0,0) ⟨hrealU hreal,hdom⟩
  have hbranch : AnalyticAt ℂ (fun ψ : CoeffPair p => (s n ψ : Coeff p)) 0 :=
    (((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.subtypeL).analyticAt (s n 0)).comp (hs.analytic n 0 hV)
  have hbranch' : AnalyticAt ℂ (fun t : ℂ × CoeffPair p => (s n t.2 : Coeff p)) (τ 0,0) := by
    simpa only [Function.comp_def] using! hbranch.comp (x := (τ 0,0)) (f := fun t : ℂ × CoeffPair p => t.2) analyticAt_snd
  have hnum := (analyticOnNhd_sourcePsiCandidate hp hp1 n (τ 0,(s n 0 : Coeff p)) (mem_univ _)).comp
    (f := fun t : ℂ × CoeffPair p => (t.1,(s n t.2 : Coeff p)))
    (analyticAt_fst.prod hbranch')
  have hR : AnalyticAt ℂ (fun t : ℂ × CoeffPair p =>
      sourceMomentRegularNumerator hp hp1 n k (s n t.2 : Coeff p) t.2 t.1) (τ 0,0) :=
    hnum.div (analyticAt_const.mul hprod)
      (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero)
        (sourceStandardRootOmittedProduct_ne_zero hp hp1 0 (τ 0) k hdom))
  have hg : AnalyticAt ℂ g (τ 0,0) := ((C.quotient_analytic k (τ 0,0) ⟨hz,hC⟩).pow 2).mul hR
  obtain ⟨U',_,_,hrealU',hcoord⟩ := exists_global_source_analytic_midpoint_squaredGap hp hp1
  have hτ : AnalyticAt ℂ τ 0 := (hcoord 0 (hrealU' hreal) k).1
  have hδ : ContinuousAt δ 0 :=
    ((continuousAt_canonicalPeriodicRight_periodOne_of_realType hp hp1 0 hreal k).sub
      (continuousAt_canonicalPeriodicLeft_periodOne_of_realType hp hp1 0 hreal k)).div_const 2
  have hδzero : δ 0 = 0 := by
    change canonicalPeriodicGap hp hp1 (periodOnePotential (0 : CoeffPair p))
      (periodOnePotential_mem 0) k / 2 = 0
    rw [show canonicalPeriodicGap hp hp1 (periodOnePotential (0 : CoeffPair p))
      (periodOnePotential_mem 0) k = 0 from by simpa only [map_zero] using canonicalPeriodicGap_zero hp hp1 k]
    exact zero_div 2
  have hm : Tendsto (fun ψ : CoeffPair p => (δ ψ,ψ)) (𝓝 0) (𝓝 (0,0)) := by
    simpa only [hδzero] using! hδ.tendsto.prodMk_nhds (tendsto_id : Tendsto (id : CoeffPair p → CoeffPair p) (𝓝 0) (𝓝 0))
  have hf := (differentiableAt_parametricSineSquareMean_zero g τ 0 hg hτ).continuousAt.tendsto.comp hm
  have hl := hf.const_mul (Complex.I/2)
  change Tendsto (C.normalizedSecondMoment s n k) (𝓝 0) (𝓝 (C.normalizedSecondMoment s n k 0))
  simpa only [normalizedSecondMoment,g,τ,δ,hδzero] using! hl

end SourceFullAbelianUniformCauchyFamily
end NLS.ZakharovShabat
