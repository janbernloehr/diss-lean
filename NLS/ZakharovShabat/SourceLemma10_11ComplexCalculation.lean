import NLS.ComplexAnalysis.CosineGapIntegralZero
import NLS.ZakharovShabat.SourceCriticalRootCommonEndpointLimit

/-!
# The complex gap-side calculation in Lemma 10.11

The primitive on the original cut disk forces the regular cosine integral
to vanish. The affine substitution then gives both actual canonical-root
boundary integrals, with their complex half-gap Jacobian. The two sheets
are pointwise opposites, fixing the orientation and the factor two before
integration. All conclusions retain the original common source domain.
-/

noncomputable section
open Set Metric Complex Filter Topology MeasureTheory intervalIntegral NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The regular cosine numerator integrates to zero on every noncollapsed
complex gap of the original source domain. -/
theorem SourceLemma10_11CircleData.cutDisc_cosineIntegral_eq_zero
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceLemma10_11CircleData hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (n : ℤ) (D : SourceCriticalRootPeriodCircle hp hp1 ψ n)
    (hδ : sourceStandardRootHalfGap hp hp1 ψ n ≠ 0) :
    (∫ θ in (0:ℝ)..Real.pi, sourceCriticalRootGapNumerator hp hp1 ψ n
      (sourceStandardRootMidpoint hp hp1 ψ n +
        sourceStandardRootHalfGap hp hp1 ψ n * (Real.cos θ:ℂ))) = 0 := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let δ := sourceStandardRootHalfGap hp hp1 ψ n
  have hl : τ-δ = l := by change (l+r)/2-(r-l)/2=l; ring
  have hr : τ+δ = r := by change (l+r)/2+(r-l)/2=r; ring
  have hE := h.previous.previous.previous.previous.previous.previous.criticalRatioExtension ψ hψ n
  have hother := D.closedBall_subset_omittedDomain
  have hroot := sourceAbelian_discComplement_subset_rootDomain hp hp1 ψ n _ _ hother
  obtain ⟨F,hF⟩ := h.exists_cutDisc_primitive ψ hψ n D
  obtain ⟨A,hA,_⟩ := h.cutDisc_common_endpoint_limit ψ hψ n D F hF
  have hi : (∫ θ in (0:ℝ)..Real.pi,
      sourceCriticalRootGapNumerator hp hp1 ψ n (cosineGapPoint τ δ (θ:ℂ))) = 0 := by
    apply integral_cosineGapPoint_eq_zero_of_primitive
      (sourceCriticalRootGapNumerator hp hp1 ψ n) (sourceStandardRoot hp hp1 ψ n)
      F (ball (D.center:ℂ) D.radius) τ δ A isOpen_ball hδ
    · rw [hl,hr]; exact D.gap
    · intro z hz
      exact (analyticAt_const.sub analyticAt_id).mul (hE z (hother (ball_subset_closedBall hz)))
    · rw [hl,hr]
      intro z hz
      exact (sourceStandardRoot_analyticAt hp hp1 ψ n z hz.2).continuousAt.continuousWithinAt
    · rw [hl,hr]
      intro z hz
      exact sourceStandardRoot_sq_of_not_mem_segment hp hp1 ψ n z hz.2
    · rw [hl,hr]
      intro z hz
      have heq : sourceCriticalRootRatioJoint hp hp1 (z,ψ) =
          sourceCriticalRootGapNumerator hp hp1 ψ n z/sourceStandardRoot hp hp1 ψ n z := by
        rw [sourceCriticalRootRatioJoint,
          sourceCriticalRootRatio_eq_selectedFactor_mul_extension hp hp1 ψ n z (hroot hz)]
        unfold sourceCriticalRootGapNumerator
        ring
      rw [← heq]
      exact hF z hz
    · rw [hl,hr]; exact hA
  simpa only [cosineGapPoint,← Complex.ofReal_cos] using hi

/-- Both selected-factor side integrals vanish for complex potentials.
A collapsed gap has zero affine Jacobian. -/
theorem SourceLemma10_11CircleData.complexGapSidePathIntegral_eq_zero
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceLemma10_11CircleData hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (n : ℤ) (D : SourceCriticalRootPeriodCircle hp hp1 ψ n) (upper : Bool) :
    gapSidePathIntegral (sourceStandardRootMidpoint hp hp1 ψ n)
      (sourceStandardRootHalfGap hp hp1 ψ n)
      (sourceCriticalRootGapNumerator hp hp1 ψ n) (-1) 1 upper = 0 := by
  by_cases hδ : sourceStandardRootHalfGap hp hp1 ψ n = 0
  · simp [gapSidePathIntegral,hδ]
  · rw [gapSidePathIntegral_eq_boundary _ _ _ 1 hδ (by norm_num) (by norm_num),
      gapSideBoundaryIntegral_eq_primitive _ _ _ 1 hδ]
    simp only [gapSidePrimitive,Real.arccos_one,
      h.cutDisc_cosineIntegral_eq_zero ψ hψ n D hδ,mul_zero]

/-- The actual full canonical-root boundary quotient pulled back from
left to right, including the complex affine Jacobian. At a collapsed
gap this is only the totalized zero-length integral convention. -/
def sourceLemma10_11ComplexSideKernel (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (upper : Bool) (t : ℝ) : ℂ :=
  sourceStandardRootHalfGap hp hp1 ψ n *
    (deriv (canonicalDiscriminant hp (periodOnePotential ψ))
      (sourceCanonicalRootGapPoint hp hp1 ψ n t) /
      (if upper then sourceCanonicalRootGapUpperValue hp hp1 ψ n t
        else sourceCanonicalRootGapLowerValue hp hp1 ψ n t))

/-- The two oriented affine kernels are exact negatives, without using
vanishing of their full integrals. -/
theorem sourceLemma10_11ComplexSideKernel_upper_eq_neg_lower
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) (t : ℝ) :
    sourceLemma10_11ComplexSideKernel hp hp1 ψ n true t =
      -sourceLemma10_11ComplexSideKernel hp hp1 ψ n false t := by
  simp only [sourceLemma10_11ComplexSideKernel,ite_true,Bool.false_eq_true,ite_false,
    sourceCanonicalRootGapUpperValue_eq_neg_lower,div_neg,mul_neg]

/-- The positive orientation goes forward along the lower side and backward
along the upper side; pointwise this is twice the lower kernel. -/
theorem sourceLemma10_11ComplexSideKernel_oriented_double
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) (t : ℝ) :
    sourceLemma10_11ComplexSideKernel hp hp1 ψ n false t -
        sourceLemma10_11ComplexSideKernel hp hp1 ψ n true t =
      2 * sourceLemma10_11ComplexSideKernel hp hp1 ψ n false t := by
  rw [sourceLemma10_11ComplexSideKernel_upper_eq_neg_lower]
  ring

/-- On the open gap, the actual boundary kernel equals the selected-factor
kernel whose square-root singularities are integrable. -/
theorem sourceLemma10_11ComplexSideKernel_eq_selectedFactor
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (D : SourceCriticalRootPeriodCircle hp hp1 ψ n)
    (hδ : sourceStandardRootHalfGap hp hp1 ψ n ≠ 0)
    (upper : Bool) (t : ℝ) (ht : t ∈ Ioo (-1) 1) :
    sourceLemma10_11ComplexSideKernel hp hp1 ψ n upper t =
      sourceCriticalRootGapNumerator hp hp1 ψ n (sourceCanonicalRootGapPoint hp hp1 ψ n t) *
        (sourceStandardRootHalfGap hp hp1 ψ n /
          ((if upper then -sourceStandardRootHalfGap hp hp1 ψ n*I
            else sourceStandardRootHalfGap hp hp1 ψ n*I) * (Real.sqrt (1-t^2):ℂ))) := by
  have hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0 := by
    intro hz
    apply hδ
    change canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n / 2 = 0
    rw [hz,zero_div]
  have hdom := D.closedBall_subset_omittedDomain (ball_subset_closedBall
    (D.gap (sourceCanonicalRootGapPoint_mem_segment hp hp1 ψ n t ht.1.le ht.2.le)))
  cases upper with
  | true =>
    simp only [sourceLemma10_11ComplexSideKernel,ite_true,
      discriminant_derivative_div_canonicalRootGapUpperValue_eq_selectedFactor hp hp1 ψ n t hgap ht hdom]
    unfold sourceCriticalRootGapNumerator
    ring
  | false =>
    simp only [sourceLemma10_11ComplexSideKernel,Bool.false_eq_true,ite_false,
      discriminant_derivative_div_canonicalRootGapLowerValue_eq_selectedFactor hp hp1 ψ n t hgap ht hdom]
    unfold sourceCriticalRootGapNumerator
    ring

/-- Endpoint integrability of the literal complex boundary kernels on the
unchanged source domain, with the degenerate convention at collapsed gaps. -/
theorem SourceLemma10_11CircleData.complexSideKernel_intervalIntegrable
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceLemma10_11CircleData hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (n : ℤ) (D : SourceCriticalRootPeriodCircle hp hp1 ψ n) (upper : Bool) :
    IntervalIntegrable (sourceLemma10_11ComplexSideKernel hp hp1 ψ n upper) volume (-1) 1 := by
  by_cases hδ : sourceStandardRootHalfGap hp hp1 ψ n = 0
  · change IntervalIntegrable (fun t => sourceLemma10_11ComplexSideKernel hp hp1 ψ n upper t) volume (-1) 1
    simp only [sourceLemma10_11ComplexSideKernel,hδ,zero_mul]
    exact intervalIntegrable_const
  · have hE := h.previous.previous.previous.previous.previous.previous.criticalRatioExtension ψ hψ n
    have hf : ContinuousOn (sourceCriticalRootGapNumerator hp hp1 ψ n)
        (standardRootGapSegment (sourceStandardRootMidpoint hp hp1 ψ n)
          (sourceStandardRootHalfGap hp hp1 ψ n)) := by
      rintro z ⟨t,ht,rfl⟩
      have hz := D.closedBall_subset_omittedDomain (ball_subset_closedBall
        (D.gap (sourceCanonicalRootGapPoint_mem_segment hp hp1 ψ n t ht.1 ht.2)))
      exact ((continuousAt_const.sub continuousAt_id).mul (hE _ hz).continuousAt).continuousWithinAt
    apply (intervalIntegrable_congr_uIoo ?_).mpr
      (gapSidePathIntegrand_intervalIntegrable _ _ _ hδ hf (-1) 1 (by norm_num) (by norm_num) upper)
    rw [uIoo_of_le (by norm_num : (-1:ℝ) ≤ 1)]
    exact fun t ht => sourceLemma10_11ComplexSideKernel_eq_selectedFactor hp hp1 ψ n D hδ upper t ht

/-- The actual affine boundary integrals vanish for every complex source
potential, on either side of the gap. -/
theorem SourceLemma10_11CircleData.complexSideIntegral_eq_zero
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceLemma10_11CircleData hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (n : ℤ) (D : SourceCriticalRootPeriodCircle hp hp1 ψ n) (upper : Bool) :
    (∫ t in (-1:ℝ)..1, sourceLemma10_11ComplexSideKernel hp hp1 ψ n upper t) = 0 := by
  by_cases hδ : sourceStandardRootHalfGap hp hp1 ψ n = 0
  · simp [sourceLemma10_11ComplexSideKernel,hδ]
  · rw [← h.complexGapSidePathIntegral_eq_zero ψ hψ n D upper]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (-1:ℝ) ≤ 1)
    exact fun t ht => sourceLemma10_11ComplexSideKernel_eq_selectedFactor hp hp1 ψ n D hδ upper t ht

/-- The literal complex calculation on every original positively oriented
circle. The factor two and side sign are fixed by the pointwise orientation
identity above; this theorem reuses the established zero period. -/
theorem SourceLemma10_11CircleData.originalCircle_complexCalculation
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (h : SourceLemma10_11CircleData hp hp1 W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψW : ψ ∈ W) (hψV : ψ ∈ V) (n : ℤ)
    (o R : ℝ) (hR : 0 < R) (hDn : D n = ball (o:ℂ) R) :
    ((∮ z in C((o:ℂ),R), sourceCriticalRootRatioJoint hp hp1 (z,ψ)) =
      2 * (∫ t in (-1:ℝ)..1, sourceLemma10_11ComplexSideKernel hp hp1 ψ n false t)) ∧
    (2 * (∫ t in (-1:ℝ)..1, sourceLemma10_11ComplexSideKernel hp hp1 ψ n false t) =
      -2 * (∫ t in (-1:ℝ)..1, sourceLemma10_11ComplexSideKernel hp hp1 ψ n true t)) ∧
    -2 * (∫ t in (-1:ℝ)..1, sourceLemma10_11ComplexSideKernel hp hp1 ψ n true t) = 0 := by
  let C := hD.periodCircle ψ hψV n o R hR hDn
  have hc : (∮ z in C((o:ℂ),R), sourceCriticalRootRatioJoint hp hp1 (z,ψ)) = 0 :=
    h.zero ψ hψW n C
  have hl := h.complexSideIntegral_eq_zero ψ hψW n C false
  have hu := h.complexSideIntegral_eq_zero ψ hψW n C true
  exact ⟨by rw [hc,hl,mul_zero],by rw [hl,hu,mul_zero,mul_zero],by rw [hu,mul_zero]⟩

end NLS.ZakharovShabat
