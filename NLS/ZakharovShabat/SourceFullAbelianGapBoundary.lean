import NLS.ZakharovShabat.SourceFullAbelianUniformEndpoints
import NLS.ZakharovShabat.SourceStandardRootGapSideSourceIntegral
import NLS.ComplexAnalysis.QuadraticPrimitiveGapBound

/-! # Actual boundary values of the normalized full primitive

The Cauchy quotient gives both side limits on each closed complex gap.
The quadratic equation bounds these values by the regular numerator.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The side is measured in the oriented coordinate of the complex gap. -/
def sourceAbelianGapSide (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (j : ℤ) (upper : Bool) : Set ℂ :=
  if upper then standardRootGapUpperSide (sourceStandardRootMidpoint hp hp1 ψ j) (sourceStandardRootHalfGap hp hp1 ψ j)
  else standardRootGapLowerSide (sourceStandardRootMidpoint hp hp1 ψ j) (sourceStandardRootHalfGap hp hp1 ψ j)

theorem sourcePeriodicSegment_eq_midpoint_segment (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (j : ℤ) :
    sourcePeriodicSegment hp hp1 ψ j = segment ℝ
      (sourceStandardRootMidpoint hp hp1 ψ j-sourceStandardRootHalfGap hp hp1 ψ j)
      (sourceStandardRootMidpoint hp hp1 ψ j+sourceStandardRootHalfGap hp hp1 ψ j) := by
  unfold sourcePeriodicSegment sourceStandardRootMidpoint sourceStandardRootHalfGap canonicalPeriodicMidpoint canonicalPeriodicGap
  congr 1 <;> ring

/-- Cosine coordinates cover the entire closed gap, even when it collapses. -/
theorem exists_sourcePeriodicSegment_cosine_parameter (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (j : ℤ) (z : ℂ) (hz : z ∈ sourcePeriodicSegment hp hp1 ψ j) :
    ∃ θ ∈ Icc (0:ℝ) Real.pi,
      sourceStandardRootMidpoint hp hp1 ψ j+sourceStandardRootHalfGap hp hp1 ψ j*(Real.cos θ:ℂ) = z := by
  rw [sourcePeriodicSegment_eq_midpoint_segment,segment_eq_image_lineMap] at hz
  obtain ⟨t,ht,rfl⟩ := hz
  refine ⟨Real.arccos (2*t-1),⟨Real.arccos_nonneg _,Real.arccos_le_pi _⟩,?_⟩
  rw [Real.cos_arccos (by linarith [ht.1] : -1 ≤ 2*t-1) (by linarith [ht.2] : 2*t-1 ≤ 1)]
  simp only [AffineMap.lineMap_apply_module,Complex.real_smul,ofReal_sub,ofReal_mul,ofReal_ofNat,ofReal_one]
  ring

theorem sourceAbelianGapSide_avoids_segment (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (j : ℤ)
    (upper : Bool) (z : ℂ) (hz : z ∈ sourceAbelianGapSide hp hp1 ψ j upper) :
    z ∉ sourcePeriodicSegment hp hp1 ψ j := by
  intro hs
  rw [sourcePeriodicSegment_eq_midpoint_segment,segment_eq_image_lineMap] at hs
  obtain ⟨t,_,rfl⟩ := hs
  have he : (AffineMap.lineMap (sourceStandardRootMidpoint hp hp1 ψ j-sourceStandardRootHalfGap hp hp1 ψ j)
      (sourceStandardRootMidpoint hp hp1 ψ j+sourceStandardRootHalfGap hp hp1 ψ j) t-sourceStandardRootMidpoint hp hp1 ψ j) /
      sourceStandardRootHalfGap hp hp1 ψ j =
      (sourceStandardRootHalfGap hp hp1 ψ j*((2*t-1:ℝ):ℂ))/sourceStandardRootHalfGap hp hp1 ψ j := by
    congr 1
    simp only [AffineMap.lineMap_apply_module,Complex.real_smul,ofReal_sub,ofReal_mul,ofReal_ofNat,ofReal_one]
    ring
  have hi : ((AffineMap.lineMap (sourceStandardRootMidpoint hp hp1 ψ j-sourceStandardRootHalfGap hp hp1 ψ j)
      (sourceStandardRootMidpoint hp hp1 ψ j+sourceStandardRootHalfGap hp hp1 ψ j) t-sourceStandardRootMidpoint hp hp1 ψ j) /
      sourceStandardRootHalfGap hp hp1 ψ j).im = 0 := by
    rw [he]
    by_cases hd : sourceStandardRootHalfGap hp hp1 ψ j = 0
    · simp [hd]
    · rw [mul_div_cancel_left₀ _ hd]; rfl
  cases upper <;> simp only [sourceAbelianGapSide, Bool.false_eq_true, ↓reduceIte,
    standardRootGapUpperSide,standardRootGapLowerSide,mem_ofPred_eq,hi,lt_self_iff_false] at hz

namespace SourceFullAbelianUniformCauchyFamily
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

/-- The boundary value of the primitive normalized at this gap. -/
def gapBoundary (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (j : ℤ) (ψ : CoeffPair p)
    (θ : ℝ) (upper : Bool) : ℂ :=
  (if upper then -I else I) * (sourceStandardRootHalfGap hp hp1 ψ j*(Real.sin θ:ℂ)*
    sourceFullAbelianCauchyQuotient hp hp1 W j (C.discs.center j) (C.discs.outer j)
      (sourceStandardRootMidpoint hp hp1 ψ j+sourceStandardRootHalfGap hp hp1 ψ j*(Real.cos θ:ℂ),ψ))

theorem gapBoundary_lower_eq_neg_upper (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (j : ℤ) (ψ : CoeffPair p) (θ : ℝ) :
    C.gapBoundary j ψ θ false = -C.gapBoundary j ψ θ true := by
  simp only [gapBoundary,Bool.false_eq_true,↓reduceIte,neg_mul,neg_neg]

theorem gapBoundary_eq_zero_of_collapsed (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (j : ℤ) (ψ : CoeffPair p)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j = 0)
    (θ : ℝ) (upper : Bool) : C.gapBoundary j ψ θ upper = 0 := by
  simp only [gapBoundary,sourceStandardRootHalfGap,hgap,zero_div,zero_mul,mul_zero]

theorem gapBoundary_norm_le (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (j : ℤ)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ j, ‖sourceCriticalRootGapNumerator hp hp1 ψ j z‖ ≤ B)
    (θ : ℝ) (hθ : θ ∈ Icc 0 Real.pi) (upper : Bool) :
    ‖C.gapBoundary j ψ θ upper‖ ≤ B*Real.pi := by
  obtain ⟨E⟩ := C.charts ψ hψ
  have hseg := C.segment_subset_outer j ψ hψ
  rw [sourcePeriodicSegment_eq_midpoint_segment] at hseg hb
  have heq := sourceFullAbelianCauchyQuotient_equation hp hp1 W ψ j _ _
    ((C.discs.inner_pos j).trans (C.discs.inner_lt j)) E (C.circle_root j ψ hψ)
    (C.discs.avoids_other ψ hψ j) (C.extension_analytic ψ hψ j)
  have hpoly : (sourceStandardRootHalfGap hp hp1 ψ j)^2 =
      (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j)^2/4 := by
    unfold sourceStandardRootHalfGap
    ring
  have h := norm_sine_mul_of_quadratic_equation _ _ _ _ _ hseg (C.quotient_slice_analytic j ψ hψ)
    (by simpa only [hpoly,sourceAngularSelectedPolynomial] using heq) B hB hb θ hθ
  cases upper <;> simpa only [gapBoundary,Bool.false_eq_true,↓reduceIte,norm_mul,norm_neg,norm_I,one_mul] using h

theorem fullPrimitive_tendsto_gapBoundary (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (j : ℤ)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j ≠ 0)
    (θ : ℝ) (hθ : θ ∈ Icc 0 Real.pi) (upper : Bool) :
    Tendsto (fun z => sourceFullAbelianPrimitive hp hp1 W j (z,ψ))
      (𝓝[sourceAbelianGapSide hp hp1 ψ j upper]
        (sourceStandardRootMidpoint hp hp1 ψ j+sourceStandardRootHalfGap hp hp1 ψ j*(Real.cos θ:ℂ)))
      (𝓝 (C.gapBoundary j ψ θ upper)) := by
  let a := sourceStandardRootMidpoint hp hp1 ψ j+sourceStandardRootHalfGap hp hp1 ψ j*(Real.cos θ:ℂ)
  have ha : a ∈ sourcePeriodicSegment hp hp1 ψ j := by
    rw [sourcePeriodicSegment_eq_midpoint_segment]
    simpa only [a,cosineGapPoint,← Complex.ofReal_cos] using
      cosineGapPoint_real_mem_segment (sourceStandardRootMidpoint hp hp1 ψ j) (sourceStandardRootHalfGap hp hp1 ψ j) θ
  have haB := C.segment_subset_outer j ψ hψ ha
  have hH := (C.quotient_slice_analytic j ψ hψ a haB).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds (s := sourceAbelianGapSide hp hp1 ψ j upper))
  have hroot : Tendsto (sourceStandardRoot hp hp1 ψ j)
      (𝓝[sourceAbelianGapSide hp hp1 ψ j upper] a)
      (𝓝 ((if upper then -I else I)*(sourceStandardRootHalfGap hp hp1 ψ j*(Real.sin θ:ℂ)))) := by
    cases upper
    · simpa only [sourceAbelianGapSide,Bool.false_eq_true,↓reduceIte,a,mul_assoc,mul_comm,mul_left_comm] using
        sourceStandardRoot_tendsto_gap_lower_cos hp hp1 ψ j θ hgap hθ.1 hθ.2
    · simpa only [sourceAbelianGapSide,↓reduceIte,a,neg_mul,mul_neg,mul_assoc,mul_comm,mul_left_comm] using
        sourceStandardRoot_tendsto_gap_upper_cos hp hp1 ψ j θ hgap hθ.1 hθ.2
  have hlim : Tendsto (fun z => sourceFullAbelianCauchyPrimitive hp hp1 W j (C.discs.center j) (C.discs.outer j) (z,ψ))
      (𝓝[sourceAbelianGapSide hp hp1 ψ j upper] a) (𝓝 (C.gapBoundary j ψ θ upper)) := by
    simpa only [sourceFullAbelianCauchyPrimitive,gapBoundary,a,mul_assoc] using hroot.mul hH
  apply hlim.congr'
  filter_upwards [mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds haB),self_mem_nhdsWithin] with z hzB hzS
  simpa only [sub_self,mul_zero,add_zero] using
    (C.fullPrimitive_eq_cauchy j j ψ hψ z ⟨hzB,sourceAbelianGapSide_avoids_segment hp hp1 ψ j upper z hzS⟩).symm

/-- On a collapsed gap the filled function agrees with the zero boundary profile. -/
theorem fullPrimitive_eq_gapBoundary_of_collapsed (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (j : ℤ) (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j = 0)
    (θ : ℝ) (upper : Bool) :
    sourceFullAbelianPrimitive hp hp1 W j
      (sourceStandardRootMidpoint hp hp1 ψ j+sourceStandardRootHalfGap hp hp1 ψ j*(Real.cos θ:ℂ),ψ) =
      C.gapBoundary j ψ θ upper := by
  rw [C.gapBoundary_eq_zero_of_collapsed j ψ hgap θ upper]
  have hr := sub_eq_zero.mp hgap
  have ha : sourceStandardRootMidpoint hp hp1 ψ j+sourceStandardRootHalfGap hp hp1 ψ j*(Real.cos θ:ℂ) =
      canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j := by
    simp only [sourceStandardRootHalfGap,hgap,zero_div,zero_mul,add_zero]
    unfold sourceStandardRootMidpoint canonicalPeriodicMidpoint
    rw [hr]
    ring
  rw [ha]
  simpa only [sub_self,mul_zero] using C.fullPrimitive_collapsed_endpoint_value j j ψ hψ hgap _ (by simp)

end SourceFullAbelianUniformCauchyFamily
end NLS.ZakharovShabat
