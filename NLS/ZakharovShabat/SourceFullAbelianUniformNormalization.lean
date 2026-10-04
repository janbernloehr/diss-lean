import NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily

/-! # All endpoint constants on the common source ball

Real-source normalization fixes each analytic offset near the real anchor.
The identity theorem propagates that value across the whole connected ball.
Consequently no gap-dependent reduction of the ball is needed.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

theorem offset_eq_of_real (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (j : ℤ)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius) :
    C.offset j φ.val = -I*(Real.pi : ℂ)*j := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) j
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) j
  let U := ball (C.discs.center j) (C.discs.outer j) \ sourcePeriodicSegment hp hp1 φ.val j
  let F := sourceAbelianPrimitive hp hp1 φ.val φ.property
  let K : ℂ → ℂ := fun z => sourceFullAbelianCauchyPrimitive hp hp1 W j (C.discs.center j) (C.discs.outer j) (z,φ.val)
  have hl : l ∈ ball (C.discs.center j) (C.discs.outer j) := C.segment_subset_outer j φ.val hφ (left_mem_segment ℝ _ _)
  have hroot : U ⊆ sourceCanonicalRootDomain hp hp1 φ.val :=
    sourceAbelian_discComplement_subset_rootDomain hp hp1 φ.val j _ _ (C.discs.avoids_other φ.val hφ j)
  let : NeBot (𝓝[U] l) := mem_closure_iff_nhdsWithin_neBot.mp
    ((dense_complex_segment_complement l r).open_subset_closure_inter isOpen_ball hl)
  have hFlim : Tendsto F (𝓝[U] l) (𝓝 (-I*(Real.pi : ℂ)*j)) :=
    (sourceAbelianPrimitive_endpoint_limit hp hp1 φ.val φ.property j l (by simp [l])).mono_left
      (nhdsWithin_mono _ (hroot.trans (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 φ.val)))
  have hKlim : Tendsto K (𝓝[U] l) (𝓝 0) :=
    sourceFullAbelianCauchyPrimitive_endpoint_limit hp hp1 W φ.val j _ _ (C.segment_subset_outer j φ.val hφ)
      (C.quotient_slice_analytic j φ.val hφ) l (by simp [l])
  have heq := primitives_eq_of_common_boundary_limit _ F (fun z => K z-I*(Real.pi : ℂ)*j) U l (-I*(Real.pi : ℂ)*j)
    (isOpen_sourceAbelian_complexDisc hp hp1 φ.val j _ _)
    (isConnected_sourceAbelian_complexDisc hp hp1 φ.val j _ _ (C.segment_subset_outer j φ.val hφ)).isPreconnected
    (fun z hz => sourceAbelianPrimitive_hasDerivAt_quotient hp hp1 φ.val φ.property z (hroot hz))
    (fun z hz => (C.primitive_hasDerivAt j φ.val hφ z hz).sub_const _) hFlim
    (by simpa only [zero_sub,neg_mul] using hKlim.sub_const (I*(Real.pi : ℂ)*j))
  have ha : C.anchor j ∈ U := ⟨(C.anchor_mem j).1,C.anchor_root j φ.val hφ j⟩
  have hval := heq ha
  obtain ⟨E⟩ := C.charts φ.val hφ
  unfold offset
  rw [sourceFullAbelianPrimitive_eq_real φ E 0 (C.anchor j)
    (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 φ.val (hroot ha))]
  simp only [Int.cast_zero,mul_zero,add_zero]
  change F (C.anchor j)-K (C.anchor j) = -I*(Real.pi : ℂ)*j
  linear_combination hval

theorem offset_eventually_eq (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (j : ℤ) :
    ∀ᶠ ψ in 𝓝 C.discs.source.val, C.offset j ψ = -I*(Real.pi : ℂ)*j := by
  have hlocal := DifferentiableOn.eventually_eq_zero_of_real_form
    (realTypeSourceLocus p) C.discs.source.val C.discs.source.property
    (by intro x y hx hy; change IsRealType (CoeffPair.toMax p (x+y)); rw [map_add]; exact hx.add hy)
    (by intro t x hx; change IsRealType (CoeffPair.toMax p ((t:ℂ) • x)); rw [map_smul]; exact hx.ofReal_smul t)
    sourceRealPart sourceImagPart sourceRealPart_realType sourceImagPart_realType
    (fun v => (sourceRealPart_add_I_smul_sourceImagPart v).symm) (norm_sourceRealPart_le hp) (norm_sourceImagPart_le hp)
    (ball C.discs.source.val C.discs.sourceRadius) isOpen_ball (mem_ball_self C.discs.sourceRadius_pos)
    (fun ψ => C.offset j ψ+I*(Real.pi : ℂ)*j)
    (fun ψ hψ => ((C.offset_analytic j ψ hψ).add analyticAt_const).differentiableAt.differentiableWithinAt)
    (by
      intro ψ hψ hreal
      rw [C.offset_eq_of_real j ⟨ψ,hreal⟩ hψ]
      ring)
  filter_upwards [hlocal] with ψ hψ
  linear_combination hψ

/-- The entire original source ball works for every normalization
constant. The local uniqueness neighborhoods do not constrain its radius. -/
theorem offset_eq (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (j : ℤ)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius) :
    C.offset j ψ = -I*(Real.pi : ℂ)*j := by
  exact (C.offset_analytic j).eqOn_of_preconnected_of_eventuallyEq
    (show AnalyticOnNhd ℂ (fun _ : CoeffPair p => -I*(Real.pi : ℂ)*j)
      (ball C.discs.source.val C.discs.sourceRadius) from fun _ _ => analyticAt_const)
    (convex_ball _ _).isPreconnected (mem_ball_self C.discs.sourceRadius_pos)
    (C.offset_eventually_eq j) hψ

/-- The full primitive equals the zero-endpoint Cauchy primitive plus
its prescribed constant on every assigned cut disc. -/
theorem fullPrimitive_eq_cauchy (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (j n : ℤ) (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius)
    (z : ℂ) (hz : z ∈ ball (C.discs.center j) (C.discs.outer j) \ sourcePeriodicSegment hp hp1 ψ j) :
    sourceFullAbelianPrimitive hp hp1 W n (z,ψ) =
      sourceFullAbelianCauchyPrimitive hp hp1 W j (C.discs.center j) (C.discs.outer j) (z,ψ)+I*(Real.pi : ℂ)*(n-j) := by
  let U := ball (C.discs.center j) (C.discs.outer j) \ sourcePeriodicSegment hp hp1 ψ j
  let F : ℂ → ℂ := fun w => sourceFullAbelianPrimitive hp hp1 W 0 (w,ψ)
  let K : ℂ → ℂ := fun w => sourceFullAbelianCauchyPrimitive hp hp1 W j (C.discs.center j) (C.discs.outer j) (w,ψ)
  have hroot : U ⊆ sourceCanonicalRootDomain hp hp1 ψ :=
    sourceAbelian_discComplement_subset_rootDomain hp hp1 ψ j _ _ (C.discs.avoids_other ψ hψ j)
  obtain ⟨E⟩ := C.charts ψ hψ
  have hF (w : ℂ) (hw : w ∈ U) := sourceFullAbelianPrimitive_hasDerivAt E 0 w (hroot hw)
  have hK (w : ℂ) (hw : w ∈ U) := C.primitive_hasDerivAt j ψ hψ w hw
  have heq : EqOn F (fun w => K w+C.offset j ψ) U :=
    (isOpen_sourceAbelian_complexDisc hp hp1 ψ j _ _).eqOn_of_deriv_eq
      (isConnected_sourceAbelian_complexDisc hp hp1 ψ j _ _ (C.segment_subset_outer j ψ hψ)).isPreconnected
      (fun w hw => (hF w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => ((hK w hw).add_const _).differentiableAt.differentiableWithinAt)
      (fun w hw => (hF w hw).deriv.trans ((hK w hw).add_const _).deriv.symm)
      (show C.anchor j ∈ U from ⟨(C.anchor_mem j).1,C.anchor_root j ψ hψ j⟩)
      (by dsimp [F,K,offset]; ring)
  rw [sourceFullAbelianPrimitive_index_shift E n z (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 ψ (hroot hz))]
  have h := heq hz
  change sourceFullAbelianPrimitive hp hp1 W 0 (z,ψ) = K z+C.offset j ψ at h
  rw [h,C.offset_eq j ψ hψ]
  dsimp [K]
  ring

/-- Both complex endpoints have the exact normalized value for every
gap on the same source ball, whether or not the gap is collapsed. -/
theorem fullPrimitive_endpoint_limit (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (j n : ℤ) (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius)
    (a : ℂ) (ha : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j} : Set ℂ)) :
    Tendsto (fun z => sourceFullAbelianPrimitive hp hp1 W n (z,ψ))
      (𝓝[ball (C.discs.center j) (C.discs.outer j) \ sourcePeriodicSegment hp hp1 ψ j] a)
      (𝓝 (I*(Real.pi : ℂ)*(n-j))) := by
  have h := (sourceFullAbelianCauchyPrimitive_endpoint_limit hp hp1 W ψ j _ _
    (C.segment_subset_outer j ψ hψ) (C.quotient_slice_analytic j ψ hψ) a ha).add_const (I*(Real.pi : ℂ)*(n-j))
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (C.fullPrimitive_eq_cauchy j n ψ hψ z hz).symm

end NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
