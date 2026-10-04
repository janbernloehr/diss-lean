import NLS.ZakharovShabat.SourceAbelianCauchyContinuation
import NLS.ZakharovShabat.SourceFloquetJointDerivative

/-! # Floquet identity and full differential inside the continued discs

Exact collar normalization propagates the exponential identity over the
connected cut disc. The zero-index continuation is consequently a local
Floquet logarithm, giving both its spectral and potential differentials.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceAbelianCauchyChart
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {j : ℤ}

/-- The prescribed collar value fixes the exponential on the whole
complex cut disc, independently of any principal logarithm branch. -/
theorem primitive_exp (D : SourceAbelianCauchyChart hp hp1 j)
    (W : Set (CoeffPair p)) (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1)
      (sourceCanonicalRootJointDomain hp hp1 W))
    (ψ : CoeffPair p) (hψ : ψ ∈ D.sources) (hψW : ψ ∈ W)
    (hnorm : D.offset ψ = -I*(Real.pi : ℂ)*j) (n : ℤ) (z : ℂ)
    (hz : z ∈ ball D.center D.radius \ sourcePeriodicSegment hp hp1 ψ j) :
    exp (D.primitive n (z,ψ)) = exp (I*(Real.pi : ℂ)*n)*sourceFloquetJointMultiplier hp hp1 (z,ψ) := by
  let U := ball D.center D.radius \ sourcePeriodicSegment hp hp1 ψ j
  let F : ℂ → ℂ := fun w => D.primitive n (w,ψ)
  let M := sourceFloquetMultiplier hp hp1 ψ
  let q : ℂ → ℂ := fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w / sourceCanonicalRoot hp hp1 ψ w
  have ha : D.anchor ∈ U := ⟨D.anchor_mem.1,D.anchor_off_segment ψ hψ⟩
  have hF (w : ℂ) (hw : w ∈ U) : HasDerivAt F (q w) w := D.primitive_derivative n ψ hψ w hw
  have hM (w : ℂ) (hw : w ∈ U) : HasDerivAt M (M w*q w) w :=
    sourceFloquetMultiplier_hasDerivAt_of_jointRoot hp hp1 W hD hroot ψ hψW w
      (sourceAbelian_discComplement_subset_rootDomain hp hp1 ψ j D.center D.radius (D.avoids_other ψ hψ) hw)
  let : NeBot (𝓝[U] D.anchor) := mem_closure_iff_nhdsWithin_neBot.mp (subset_closure ha)
  have hFlim : Tendsto (fun w => F w-F D.anchor) (𝓝[U] D.anchor) (𝓝 0) := by
    have hc : ContinuousAt (fun w => F w-F D.anchor) D.anchor :=
      ((hF D.anchor ha).sub_const (F D.anchor)).continuousAt
    simpa only [sub_self] using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := U))
  have hprop := multiplier_eq_exp_of_normalized_primitive q (fun w => F w-F D.anchor) M U D.anchor (M D.anchor)
    (isOpen_sourceAbelian_complexDisc hp hp1 ψ j D.center D.radius)
    (isConnected_sourceAbelian_complexDisc hp hp1 ψ j D.center D.radius (D.segment_subset_outer ψ hψ)).isPreconnected
    (fun w hw => (hF w hw).sub_const _) hM hFlim (hM D.anchor ha).continuousAt.continuousWithinAt.tendsto z hz
  have hanchor : exp (F D.anchor) = exp (I*(Real.pi : ℂ)*n)*M D.anchor := by
    change exp (D.primitive n (D.anchor,ψ)) = _
    have he := D.primitive_eq_joint_on_collar ψ hψ hnorm n D.anchor_mem
    dsimp only at he
    rw [he]
    exact sourceAbelianJointPrimitive_exp hp hp1 n (D.anchor,ψ) (D.anchor_joint ψ hψ)
  change exp (F z) = exp (I*(Real.pi : ℂ)*n)*M z
  calc
    exp (F z) = exp (F D.anchor)*exp (F z-F D.anchor) := by rw [← exp_add]; congr 1; ring
    _ = exp (I*(Real.pi : ℂ)*n)*M z := by rw [hanchor,hprop]; ring

/-- The exact zero-index local logarithm germ on the interior domain. -/
theorem primitive_zero_germ (D : SourceAbelianCauchyChart hp hp1 j)
    (W : Set (CoeffPair p)) (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1)
      (sourceCanonicalRootJointDomain hp hp1 W))
    (hnorm : ∀ ψ ∈ D.sources, D.offset ψ = -I*(Real.pi : ℂ)*j)
    (t : ℂ × CoeffPair p)
    (ht : t ∈ sourceCanonicalRootJointDomain hp hp1 W)
    (hball : t.1 ∈ ball D.center D.radius) (hsource : t.2 ∈ D.sources) :
    normalizedLogChart (sourceFloquetJointMultiplier hp hp1) t (D.primitive 0 t) =ᶠ[𝓝 t] D.primitive 0 := by
  apply normalizedLogChart_eventually_eq _ _ t (D.primitive_analytic 0 t ⟨hball,hsource,ht.2 j⟩).continuousAt
  filter_upwards [hD.mem_nhds ht, (isOpen_ball.prod D.sources_open).mem_nhds ⟨hball,hsource⟩] with u hu hv
  simpa only [Int.cast_zero,mul_zero,exp_zero,one_mul] using
    D.primitive_exp W hD hroot u.2 hv.2 hu.1 (hnorm u.2 hv.2) 0 u.1 ⟨hv.1,hu.2 j⟩

/-- The full joint differential on the new interior agrees with the
same discriminant quotient as the original collar and exterior. -/
theorem primitive_hasFDerivAt (D : SourceAbelianCauchyChart hp hp1 j)
    (W : Set (CoeffPair p)) (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1)
      (sourceCanonicalRootJointDomain hp hp1 W))
    (hnorm : ∀ ψ ∈ D.sources, D.offset ψ = -I*(Real.pi : ℂ)*j)
    (n : ℤ) (t : ℂ × CoeffPair p)
    (ht : t ∈ sourceCanonicalRootJointDomain hp hp1 W)
    (hball : t.1 ∈ ball D.center D.radius) (hsource : t.2 ∈ D.sources) :
    HasFDerivAt (D.primitive n)
      ((sourceCanonicalRoot hp hp1 t.2 t.1)⁻¹ •
        fderiv ℂ (fun u : ℂ × CoeffPair p => canonicalDiscriminant hp (periodOnePotential u.2) u.1) t) t := by
  have hne : sourceFloquetJointMultiplier hp hp1 t ≠ 0 := sourceFloquetMultiplier_ne_zero hp hp1 t.2 t.1 ht.2
  have hlog : sourceFloquetJointMultiplier hp hp1 t/sourceFloquetJointMultiplier hp hp1 t ∈ slitPlane := by
    rw [div_self hne]
    simp
  have h0 := (normalizedLogChart_sourceFloquet_hasFDerivAt hp hp1 W hD hroot t t
    (D.primitive 0 t) ht ht hlog).congr_of_eventuallyEq (D.primitive_zero_germ W hD hroot hnorm t ht hball hsource).symm
  simpa only [primitive,Int.cast_zero,mul_zero,add_zero] using! h0.add_const (I*(Real.pi : ℂ)*n)

/-- The potential gradient from Lemma 19.1(i) throughout each new
complex-source cut disc, with every normalization index. -/
theorem primitive_source_fderiv (D : SourceAbelianCauchyChart hp hp1 j)
    (W : Set (CoeffPair p)) (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1)
      (sourceCanonicalRootJointDomain hp hp1 W))
    (hnorm : ∀ ψ ∈ D.sources, D.offset ψ = -I*(Real.pi : ℂ)*j)
    (n : ℤ) (z : ℂ) (ψ h : CoeffPair p)
    (ht : (z,ψ) ∈ sourceCanonicalRootJointDomain hp hp1 W)
    (hz : z ∈ ball D.center D.radius) (hψ : ψ ∈ D.sources) :
    (fderiv ℂ (fun χ : CoeffPair p => D.primitive n (z,χ)) ψ) h =
      (fderiv ℂ (fun χ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential χ) z) ψ) h /
        sourceCanonicalRoot hp hp1 ψ z := by
  have hjoint := D.primitive_hasFDerivAt W hD hroot hnorm n (z,ψ) ht hz hψ
  rw [fderiv_source_section_eq_joint _ z ψ hjoint.differentiableAt,hjoint.fderiv,
    fderiv_source_section_eq_joint _ z ψ
      (analyticOnNhd_canonicalDiscriminant_periodOne hp hp1 (z,ψ) (mem_univ _)).differentiableAt]
  simp only [ContinuousLinearMap.comp_apply,smul_apply,smul_eq_mul,div_eq_inv_mul]

end NLS.ZakharovShabat.SourceAbelianCauchyChart
