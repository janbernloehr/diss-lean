import NLS.SequenceSpaces.ReciprocalSquareDensityIntegral
import NLS.ZakharovShabat.SourceExteriorGapCorrection

/-! # Index decay of the actual exterior correction

Separation of all points of distinct real gaps bounds the exterior kernel
by a reciprocal-square index kernel. A weighted action-density majorant
then controls the full correction integral, including infinitely many gaps.
-/

noncomputable section
open Set Metric Complex MeasureTheory
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Index-scale segment separation gives the corresponding real exterior distances. -/
theorem sourceRealGaps_index_exterior_separation (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (C : ℝ) (hC : 1 ≤ C)
    (hsep : ∀ i j : ℤ, i ≠ j → ∀ z ∈ sourcePeriodicSegment hp hp1 φ.val i,
      ∀ w ∈ sourcePeriodicSegment hp hp1 φ.val j, |((i-j:ℤ):ℝ)| ≤ C*‖w-z‖)
    (n m : ℤ) (hm : m ≠ n) :
    let L : ℤ → ℝ := fun k => (canonicalPeriodicLeft hp hp1
      (periodOnePotential φ.val) (periodOnePotential_mem φ.val) k).re
    let R : ℤ → ℝ := fun k => (canonicalPeriodicRight hp hp1
      (periodOnePotential φ.val) (periodOnePotential_mem φ.val) k).re
    let δ : ℝ := |((n-m:ℤ):ℝ)|/C
    0 < δ ∧ ∀ x ∈ Icc (L m) (R m),
      δ ≤ |x-L n| ∧ δ ≤ |x-R n| ∧ (R n-L n)/2+δ ≤ |x-(L n+R n)/2| := by
  dsimp only
  let L : ℤ → ℝ := fun k => (canonicalPeriodicLeft hp hp1
    (periodOnePotential φ.val) (periodOnePotential_mem φ.val) k).re
  let R : ℤ → ℝ := fun k => (canonicalPeriodicRight hp hp1
    (periodOnePotential φ.val) (periodOnePotential_mem φ.val) k).re
  let δ : ℝ := |((n-m:ℤ):ℝ)|/C
  change 0 < δ ∧ ∀ x ∈ Icc (L m) (R m),
    δ ≤ |x-L n| ∧ δ ≤ |x-R n| ∧ (R n-L n)/2+δ ≤ |x-(L n+R n)/2|
  have hCp : 0 < C := by linarith
  have hd : 0 < |((n-m:ℤ):ℝ)| := abs_pos.mpr (by exact_mod_cast sub_ne_zero.mpr hm.symm)
  have hab (k : ℤ) : L k ≤ R k := NLS.ComplexAnalysis.re_le_of_complexLexLE
    ((canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val)).2.1 k)
  refine ⟨div_pos hd hCp,?_⟩
  intro x hx
  have hpoint (y : ℝ) (hy : y ∈ Icc (L n) (R n)) : δ ≤ |x-y| := by
    have h := hsep n m hm.symm (y:ℂ)
      (sourcePeriodicSegment_mem_of_realIcc hp hp1 φ.val φ.property n y hy) (x:ℂ)
      (sourcePeriodicSegment_mem_of_realIcc hp hp1 φ.val φ.property m x hx)
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at h
    exact (div_le_iff₀ hCp).mpr (by simpa only [mul_comm] using h)
  have hl := hpoint (L n) ⟨le_rfl,hab n⟩
  have hr := hpoint (R n) ⟨hab n,le_rfl⟩
  refine ⟨hl,hr,?_⟩
  rcases lt_or_gt_of_ne hm with hmn | hnm
  · have hxm : x ≤ L n := hx.2.trans (canonicalPeriodicRight_re_lt_left_of_lt hp hp1
      (periodOnePotential φ.val) (periodOnePotential_mem φ.val)
      (isRealType_periodOnePotential φ.val φ.property) hmn).le
    rw [abs_of_nonpos (by linarith : x-L n ≤ 0)] at hl
    rw [abs_of_nonpos (by linarith [hab n] : x-(L n+R n)/2 ≤ 0)]
    linarith
  · have hxm : R n ≤ x := (canonicalPeriodicRight_re_lt_left_of_lt hp hp1
      (periodOnePotential φ.val) (periodOnePotential_mem φ.val)
      (isRealType_periodOnePotential φ.val φ.property) hnm).le.trans hx.1
    rw [abs_of_nonneg (by linarith : 0 ≤ x-R n)] at hr
    rw [abs_of_nonneg (by linarith [hab n] : 0 ≤ x-(L n+R n)/2)]
    linarith

/-- The actual positive exterior kernel has a reciprocal-square index majorant. -/
theorem sourceExteriorGapKernel_le_index_majorant (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (C : ℝ) (hC : 1 ≤ C)
    (hsep : ∀ i j : ℤ, i ≠ j → ∀ z ∈ sourcePeriodicSegment hp hp1 φ.val i,
      ∀ w ∈ sourcePeriodicSegment hp hp1 φ.val j, |((i-j:ℤ):ℝ)| ≤ C*‖w-z‖)
    (n : ℤ) (hg : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (z : {m : ℤ // m ≠ n} × ℝ) (θ : ℝ) :
    sourceExteriorGapKernelWeight hp hp1 φ n z / |sourceExteriorGapPole hp hp1 φ n z-Real.cos θ| ≤
      C^2*sourceGapAngularDensity hp hp1 φ z.1.val z.2/|((n-z.1.val:ℤ):ℝ)|^2 := by
  let δ : ℝ := |((n-z.1.val:ℤ):ℝ)|/C
  obtain ⟨hδ,hd⟩ := sourceRealGaps_index_exterior_separation hp hp1 φ C hC hsep n z.1.val z.1.property
  have hdist := hd _ (realGapAffinePoint_cos_mem_Icc hp hp1 φ z.1.val z.2)
  have hv : δ ≤ sourceExteriorGapRoot hp hp1 φ n z :=
    NLS.ComplexAnalysis.separated_gap_sqrt_lower_bound _ _ _ δ hδ.le hdist.1 hdist.2.1
  have hpole := NLS.ComplexAnalysis.separated_gap_normalized_pole
    (sourceGapHalfWidthReal hp hp1 φ n) (sourceGapCenterReal hp hp1 φ n) _ δ
    (sourceGapHalfWidthReal_pos hp hp1 φ n hg) hδ hdist.2.2
  have hbound := NLS.ComplexAnalysis.exterior_gap_kernel_majorant _ _ _ _ δ
    (sourceGapAngularDensity_nonneg hp hp1 φ z.1.val z.2)
    (sourceGapHalfWidthReal_pos hp hp1 φ n hg) hδ hv hpole.1
  have hk := NLS.ComplexAnalysis.exterior_cosine_kernel_norm_le
    (sourceExteriorGapKernelWeight hp hp1 φ n z) (sourceExteriorGapPole hp hp1 φ n z) θ
    (sourceExteriorGapKernelWeight_nonneg hp hp1 φ n hg z) hpole.2
  calc
    _ ≤ ‖sourceExteriorGapKernelWeight hp hp1 φ n z / |sourceExteriorGapPole hp hp1 φ n z-Real.cos θ|‖ :=
      Real.le_norm_self _
    _ ≤ sourceExteriorGapKernelWeight hp hp1 φ n z/(|sourceExteriorGapPole hp hp1 φ n z|-1) := hk
    _ ≤ sourceGapAngularDensity hp hp1 φ z.1.val z.2/δ^2 := hbound
    _ = _ := by dsimp [δ]; field_simp

end NLS.ZakharovShabat


namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual exterior correction has inverse-square-bracket decay under a weighted mass bound. -/
theorem sourceExteriorGapCorrection_weighted_bound (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (C : ℝ) (hC : 1 ≤ C)
    (hsep : ∀ i j : ℤ, i ≠ j → ∀ z ∈ sourcePeriodicSegment hp hp1 φ.val i,
      ∀ w ∈ sourcePeriodicSegment hp hp1 φ.val j, |((i-j:ℤ):ℝ)| ≤ C*‖w-z‖)
    (a : Coeff 1)
    (hmass : ∀ m : ℤ, (∫ θ : ℝ, sourceGapAngularDensity hp hp1 φ m θ) ≤ ‖a m‖/(1+|(m:ℝ)|)^2)
    (n : ℤ) (hg : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (θ : ℝ) :
    (1+|(n:ℝ)|)^2*sourceExteriorGapCorrection hp hp1 φ n θ ≤ 4*C^2*‖a‖ := by
  obtain ⟨hi,hb⟩ := Coeff.reciprocal_square_density_integral_bound a
    (sourceGapAngularDensity hp hp1 φ) (measurable_sourceGapAngularDensity hp hp1 φ)
    (integrable_sourceGapAngularDensity hp hp1 φ) (sourceGapAngularDensity_nonneg hp hp1 φ) hmass n
  let f := fun z : {m : ℤ // m ≠ n} × ℝ =>
    sourceGapAngularDensity hp hp1 φ z.1.val z.2/|((n-z.1.val:ℤ):ℝ)|^2
  let g := fun z : {m : ℤ // m ≠ n} × ℝ =>
    sourceExteriorGapKernelWeight hp hp1 φ n z/|sourceExteriorGapPole hp hp1 φ n z-Real.cos θ|
  have hgn (z) : 0 ≤ g z :=
    div_nonneg (sourceExteriorGapKernelWeight_nonneg hp hp1 φ n hg z) (abs_nonneg _)
  have hbound (z) : g z ≤ C^2*f z := by
    simpa only [f,g,mul_div_assoc] using sourceExteriorGapKernel_le_index_majorant hp hp1 φ C hC hsep n hg z θ
  have hgm : Measurable g := (measurable_sourceExteriorGapKernelWeight hp hp1 φ n).div
    ((measurable_sourceExteriorGapPole hp hp1 φ n).sub measurable_const).norm
  have hgi : Integrable g (Measure.count.prod volume) := (hi.const_mul (C^2)).mono'
    hgm.aestronglyMeasurable (Filter.Eventually.of_forall (fun z => by
      rw [Real.norm_of_nonneg (hgn z)]
      exact hbound z))
  have hV : sourceExteriorGapCorrection hp hp1 φ n θ ≤
      C^2*(∫ z, f z ∂(Measure.count.prod volume)) := by
    simpa only [sourceExteriorGapCorrection,integral_const_mul] using integral_mono hgi (hi.const_mul (C^2)) hbound
  calc
    _ ≤ (1+|(n:ℝ)|)^2*(C^2*(∫ z, f z ∂(Measure.count.prod volume))) :=
      mul_le_mul_of_nonneg_left hV (sq_nonneg _)
    _ = C^2*((1+|(n:ℝ)|)^2*(∫ z, f z ∂(Measure.count.prod volume))) := by ring
    _ ≤ C^2*(4*‖a‖) := mul_le_mul_of_nonneg_left hb (sq_nonneg C)
    _ = _ := by ring

end NLS.ZakharovShabat
