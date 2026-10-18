import NLS.ZakharovShabat.SourceExteriorGapKernel
import NLS.ZakharovShabat.SourcePrimitivePowerRealIntegral
import NLS.ZakharovShabat.SourceFullAbelianUniformNormalization

/-! # The analytically filled spectral quotient

The actual quotient -i*F_n/root_n extends across the selected gap. Its
values recover the real cosine profile, and its boundary jumps on all
other gaps retain the exact normalization. The positive exterior-kernel
representation is not assumed or proved here.
-/

noncomputable section
open Set Metric Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
variable (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)

/-- The normalized primitive/root quotient, filled analytically across the selected gap. -/
def filledGapQuotient (n : ℤ) (ψ : CoeffPair p) (z : ℂ) : ℂ := by
  classical
  exact if z ∈ ball (C.discs.center n) (C.discs.outer n) then
    -I * sourceFullAbelianCauchyQuotient hp hp1 W n (C.discs.center n) (C.discs.outer n) (z,ψ)
  else -I * (sourceFullAbelianPrimitive hp hp1 W n (z,ψ) / sourceStandardRoot hp hp1 ψ n z)

theorem filledGapQuotient_eq_local (n : ℤ) (ψ : CoeffPair p) (z : ℂ)
    (hz : z ∈ ball (C.discs.center n) (C.discs.outer n)) :
    C.filledGapQuotient n ψ z =
      -I * sourceFullAbelianCauchyQuotient hp hp1 W n (C.discs.center n) (C.discs.outer n) (z,ψ) := by
  simp only [filledGapQuotient,if_pos hz]

theorem filledGapQuotient_eq_div (n : ℤ) (ψ : CoeffPair p)
    (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius) (z : ℂ)
    (hz : z ∉ sourcePeriodicSegment hp hp1 ψ n) :
    C.filledGapQuotient n ψ z =
      -I * (sourceFullAbelianPrimitive hp hp1 W n (z,ψ) / sourceStandardRoot hp hp1 ψ n z) := by
  by_cases hb : z ∈ ball (C.discs.center n) (C.discs.outer n)
  · rw [C.filledGapQuotient_eq_local n ψ z hb,C.fullPrimitive_eq_cauchy n n ψ hψ z ⟨hb,hz⟩]
    simp only [sub_self,mul_zero,add_zero,sourceFullAbelianCauchyPrimitive]
    rw [mul_div_cancel_left₀ _ (sourceStandardRoot_ne_zero_off_segment hp hp1 ψ n z hz)]
  · simp only [filledGapQuotient,if_neg hb]

/-- The selected gap is completely filled; only other open cuts remain excluded. -/
theorem filledGapQuotient_analytic (n : ℤ) (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius) :
    AnalyticOnNhd ℂ (C.filledGapQuotient n φ.val)
      ((sourceOpenGapComplement hp hp1 φ.val \ sourcePeriodicSegment hp hp1 φ.val n) ∪
        ball (C.discs.center n) (C.discs.outer n)) := by
  obtain ⟨E⟩ := C.charts φ.val hφ
  intro z hz
  by_cases hb : z ∈ ball (C.discs.center n) (C.discs.outer n)
  · apply (analyticAt_const.mul (C.quotient_slice_analytic n φ.val hφ z hb)).congr
    filter_upwards [isOpen_ball.mem_nhds hb] with w hw
    exact (C.filledGapQuotient_eq_local n φ.val w hw).symm
  · have hzo := (hz.resolve_right hb).1
    have hzs := (hz.resolve_right hb).2
    have ha := (sourceFullAbelianPrimitive_spectral_analytic E n z hzo).div
      (sourceStandardRoot_analyticAt hp hp1 φ.val n z hzs)
      (sourceStandardRoot_ne_zero_off_segment hp hp1 φ.val n z hzs)
    apply (analyticAt_const.mul ha).congr
    filter_upwards [(isClosed_sourcePeriodicSegment hp hp1 φ.val n).isOpen_compl.mem_nhds hzs] with w hw
    exact (C.filledGapQuotient_eq_div n φ.val hφ w hw).symm

/-- On the real cosine gap the quotient gives the exact profile, including both endpoints. -/
theorem real_profile_eq_filledGapQuotient (n : ℤ) (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (θ : ℝ) (hθ : θ ∈ Icc (0:ℝ) Real.pi) :
    sourceRealGapCosineProfile hp hp1 φ.val n θ =
      sourceGapHalfWidthReal hp hp1 φ n * Real.sin θ *
        (C.filledGapQuotient n φ.val (sourceCanonicalRootGapPoint hp hp1 φ.val n (Real.cos θ))).re := by
  have hz := sourceCanonicalRootGapPoint_mem_segment hp hp1 φ.val n (Real.cos θ)
    (Real.neg_one_le_cos θ) (Real.cos_le_one θ)
  rw [C.filledGapQuotient_eq_local n φ.val _ (C.segment_subset_outer n φ.val hφ hz)]
  have h := C.gapBoundary_eq_realCosineProfile n φ hφ hg θ hθ
  rw [gapBoundary,if_pos rfl,sourceStandardRootHalfGap_eq_ofReal_affineJacobian hp hp1 φ.val φ.property n] at h
  have he : (sourceRealGapCosineProfile hp hp1 φ.val n θ : ℂ) =
      (sourceGapHalfWidthReal hp hp1 φ n : ℂ) * (Real.sin θ : ℂ) *
        (-I * sourceFullAbelianCauchyQuotient hp hp1 W n (C.discs.center n) (C.discs.outer n)
          (sourceCanonicalRootGapPoint hp hp1 φ.val n (Real.cos θ),φ.val)) := by
    rw [← h]
    unfold sourceGapHalfWidthReal sourceCanonicalRootGapPoint
    rw [sourceStandardRootHalfGap_eq_ofReal_affineJacobian hp hp1 φ.val φ.property n]
    ring
  simpa only [ofReal_re,mul_re,mul_im,ofReal_im,zero_mul,mul_zero,add_zero,sub_zero] using congrArg Complex.re he

/-- The filled quotient has a strictly positive real part on the interior of an open real gap. -/
theorem filledGapQuotient_re_pos_on_gap (n : ℤ) (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi) :
    0 < (C.filledGapQuotient n φ.val (sourceCanonicalRootGapPoint hp hp1 φ.val n (Real.cos θ))).re := by
  have h := sourceRealGapCosineProfile_pos hp hp1 φ n hg θ hθ
  rw [C.real_profile_eq_filledGapQuotient n φ hφ hg θ ⟨hθ.1.le,hθ.2.le⟩] at h
  exact (mul_pos_iff_of_pos_left (mul_pos (sourceGapHalfWidthReal_pos hp hp1 φ n hg)
    (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2))).mp h


/-- The exact exterior-gap boundary constants of the filled normalized quotient. -/
theorem filledGapQuotient_other_gap_boundary_limit (n m : ℤ) (hmn : m ≠ n)
    (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius) (upper : Bool) (x : ℝ)
    (hx : x ∈ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m).re) :
    Tendsto (C.filledGapQuotient n φ.val)
      (𝓝[sourceAbelianHalfPlane upper] (x:ℂ))
      (𝓝 (-I * (((if upper then (sourceRealGapArcoshProfile hp φ.val m x : ℂ)
        else -(sourceRealGapArcoshProfile hp φ.val m x : ℂ))+I*(Real.pi:ℂ)*(n-m)) /
        sourceStandardRoot hp hp1 φ.val n (x:ℂ)))) := by
  obtain ⟨V,_,_,hreal,hdisj⟩ := exists_global_source_disjoint_periodicSegments hp hp1
  have hxm := sourcePeriodicSegment_mem_of_realIcc hp hp1 φ.val φ.property m x hx
  have hxn : (x:ℂ) ∉ sourcePeriodicSegment hp hp1 φ.val n :=
    Set.disjoint_left.mp (hdisj φ.val (hreal φ.property) m n hmn) hxm
  obtain ⟨E⟩ := C.charts φ.val hφ
  have hF := sourceFullAbelianPrimitive_real_gap_boundary_limit_index φ E m n upper x hx
  have hQ := (sourceStandardRoot_analyticAt hp hp1 φ.val n (x:ℂ) hxn).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds (s := sourceAbelianHalfPlane upper))
  have hlim := (tendsto_const_nhds (x := -I)).mul (hF.div hQ
    (sourceStandardRoot_ne_zero_off_segment hp hp1 φ.val n (x:ℂ) hxn))
  apply hlim.congr'
  filter_upwards [nhdsWithin_le_nhds ((isClosed_sourcePeriodicSegment hp hp1 φ.val n).isOpen_compl.mem_nhds hxn)] with z hz
  exact (C.filledGapQuotient_eq_div n φ.val hφ z hz).symm

/-- The signed index offset cancels from the jump across any other gap. -/
theorem normalized_gap_quotient_jump (v q a : ℂ) :
    -I*((v+a)/q)-(-I*((-v+a)/q)) = -2*I*(v/q) := by
  simp only [div_eq_mul_inv]
  ring

end NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
