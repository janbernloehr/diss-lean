import NLS.ZakharovShabat.SourceFullAbelianJointAnalytic

/-! # Exact joint differential of the full spectral primitive

Spectral uniqueness propagates the Floquet exponential identity from the
exterior. Joint analyticity then identifies the local normalized logarithm,
giving the full differential at every off-cut interior point.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)} {ψ : CoeffPair p}

/-- The exact Floquet exponential identity holds on the whole complex
cut complement for the canonical primitive. -/
theorem sourceFullAbelianPrimitive_exp (D : SourceAbelianSpectralChart hp hp1 W ψ)
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (n : ℤ) (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    exp (sourceFullAbelianPrimitive hp hp1 W n (z,ψ)) =
      exp (I*(Real.pi : ℂ)*n)*sourceFloquetJointMultiplier hp hp1 (z,ψ) := by
  let F := fun w => exp (sourceFullAbelianPrimitive hp hp1 W n (w,ψ))
  let G := fun w => exp (I*(Real.pi : ℂ)*n)*sourceFloquetJointMultiplier hp hp1 (w,ψ)
  have hM := sourceFloquetJointMultiplier_analyticOnNhd hp hp1 W hroot
  have hF : AnalyticOnNhd ℂ F (sourceCanonicalRootDomain hp hp1 ψ) := fun w hw =>
    (sourceFullAbelianPrimitive_spectral_analytic D n w
      (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 ψ hw)).cexp'
  have hG : AnalyticOnNhd ℂ G (sourceCanonicalRootDomain hp hp1 ψ) := by
    intro w hw
    exact analyticAt_const.mul ((hM (w,ψ) ⟨D.discs.source_subset D.source_mem,hw⟩).comp
      (f := fun w : ℂ => (w,ψ)) (analyticAt_id.prod analyticAt_const))
  obtain ⟨c,hc⟩ := D.discs.exterior_nonempty
  have hcΓ : (c,ψ) ∈ sourceAbelianProjectedDomain hp hp1 W := D.discs.exterior_product_subset_projected ⟨hc,D.source_mem⟩
  have hfg : F =ᶠ[𝓝 c] G := by
    filter_upwards [D.discs.isOpen_exterior.mem_nhds hc] with w hw
    have hwΓ : (w,ψ) ∈ sourceAbelianProjectedDomain hp hp1 W := D.discs.exterior_product_subset_projected ⟨hw,D.source_mem⟩
    have hwroot := (sourceAbelianProjectedDomain_end hp hp1 W hwΓ).2
    dsimp only [F,G]
    rw [sourceFullAbelianPrimitive_eq_chart D n w
      (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 ψ hwroot),D.exterior_eq n hw]
    exact sourceAbelianProjectedPrimitive_exp hp hp1 W hM n (w,ψ) hwΓ
  exact hF.eqOn_of_preconnected_of_eventuallyEq hG (D.discs.isConnected_rootDomain ψ D.source_mem).isPreconnected
    (sourceAbelianProjectedDomain_end hp hp1 W hcΓ).2 hfg hz

namespace SourceAbelianUniformDiscFamily
variable (D : SourceAbelianUniformDiscFamily hp hp1 W)
variable (hall : ∀ χ ∈ ball D.source.val D.sourceRadius,
  ∃ E : SourceAbelianSpectralChart hp hp1 W χ, E.discs = D)
variable (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
variable (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))

include hD in
theorem isOpen_rootJointDomain :
    IsOpen (sourceCanonicalRootJointDomain hp hp1 (ball D.source.val D.sourceRadius)) := by
  have heq : sourceCanonicalRootJointDomain hp hp1 (ball D.source.val D.sourceRadius) =
      sourceCanonicalRootJointDomain hp hp1 W ∩ (Prod.snd ⁻¹' ball D.source.val D.sourceRadius) := by
    ext t
    exact ⟨fun ht => ⟨⟨D.source_subset ht.1,ht.2⟩,ht.1⟩,fun ht => ⟨ht.2,ht.1.2⟩⟩
  rw [heq]
  exact hD.inter (isOpen_ball.preimage continuous_snd)

include hall hD hroot in
theorem fullPrimitive_zero_germ (t : ℂ × CoeffPair p)
    (ht : t ∈ sourceCanonicalRootJointDomain hp hp1 (ball D.source.val D.sourceRadius)) :
    normalizedLogChart (sourceFloquetJointMultiplier hp hp1) t (sourceFullAbelianPrimitive hp hp1 W 0 t)
      =ᶠ[𝓝 t] sourceFullAbelianPrimitive hp hp1 W 0 := by
  apply normalizedLogChart_eventually_eq _ _ t (D.fullPrimitive_joint_analytic hall hD hroot 0 t ht).continuousAt
  filter_upwards [(D.isOpen_rootJointDomain hD).mem_nhds ht] with u hu
  obtain ⟨E,_⟩ := hall u.2 hu.1
  simpa only [Int.cast_zero,mul_zero,exp_zero,one_mul] using sourceFullAbelianPrimitive_exp E hroot 0 u.1 hu.2

include hall hD hroot in
/-- Exact joint differential on the full interior and exterior domain. -/
theorem fullPrimitive_joint_hasFDerivAt (n : ℤ) (t : ℂ × CoeffPair p)
    (ht : t ∈ sourceCanonicalRootJointDomain hp hp1 (ball D.source.val D.sourceRadius)) :
    HasFDerivAt (sourceFullAbelianPrimitive hp hp1 W n)
      ((sourceCanonicalRoot hp hp1 t.2 t.1)⁻¹ •
        fderiv ℂ (fun u : ℂ × CoeffPair p => canonicalDiscriminant hp (periodOnePotential u.2) u.1) t) t := by
  have htW : t ∈ sourceCanonicalRootJointDomain hp hp1 W := ⟨D.source_subset ht.1,ht.2⟩
  have hne : sourceFloquetJointMultiplier hp hp1 t ≠ 0 := sourceFloquetMultiplier_ne_zero hp hp1 t.2 t.1 ht.2
  have hlog : sourceFloquetJointMultiplier hp hp1 t/sourceFloquetJointMultiplier hp hp1 t ∈ slitPlane := by
    rw [div_self hne]
    simp
  have h0 := (normalizedLogChart_sourceFloquet_hasFDerivAt hp hp1 W hD hroot t t
    (sourceFullAbelianPrimitive hp hp1 W 0 t) htW htW hlog).congr_of_eventuallyEq
      (D.fullPrimitive_zero_germ hall hD hroot t ht).symm
  apply (h0.add_const (I*(Real.pi : ℂ)*n)).congr_of_eventuallyEq
  filter_upwards [(D.isOpen_rootJointDomain hD).mem_nhds ht] with u hu
  obtain ⟨E,_⟩ := hall u.2 hu.1
  exact sourceFullAbelianPrimitive_index_shift E n u.1
    (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 u.2 hu.2)

include hall hD hroot in
/-- The potential gradient from Lemma 19.1(i), now at all interior points. -/
theorem fullPrimitive_source_fderiv (n : ℤ) (z : ℂ) (ψ h : CoeffPair p)
    (ht : (z,ψ) ∈ sourceCanonicalRootJointDomain hp hp1 (ball D.source.val D.sourceRadius)) :
    (fderiv ℂ (fun χ : CoeffPair p => sourceFullAbelianPrimitive hp hp1 W n (z,χ)) ψ) h =
      (fderiv ℂ (fun χ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential χ) z) ψ) h /
        sourceCanonicalRoot hp hp1 ψ z := by
  have hjoint := D.fullPrimitive_joint_hasFDerivAt hall hD hroot n (z,ψ) ht
  rw [fderiv_source_section_eq_joint _ z ψ hjoint.differentiableAt,hjoint.fderiv,
    fderiv_source_section_eq_joint _ z ψ
      (analyticOnNhd_canonicalDiscriminant_periodOne hp hp1 (z,ψ) (mem_univ _)).differentiableAt]
  simp only [ContinuousLinearMap.comp_apply,smul_apply,smul_eq_mul,div_eq_inv_mul]

end SourceAbelianUniformDiscFamily

/-- A single almost-real neighborhood supports the full primitive,
its filled spectral slices and its exact joint differential everywhere
off the moving cuts. -/
theorem exists_sourceFullAbelian_almostReal_differential (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W V : Set (CoeffPair p), IsOpen W ∧ IsOpen V ∧ IsConnected V ∧
      realTypeSourceLocus p ⊆ V ∧ V ⊆ W ∧
      (∀ ψ ∈ V, Nonempty (SourceAbelianSpectralChart hp hp1 W ψ)) ∧
      ∀ n : ℤ, AnalyticOnNhd ℂ (sourceFullAbelianPrimitive hp hp1 W n)
        (sourceCanonicalRootJointDomain hp hp1 V) ∧
        ∀ t ∈ sourceCanonicalRootJointDomain hp hp1 V,
          HasFDerivAt (sourceFullAbelianPrimitive hp hp1 W n)
            ((sourceCanonicalRoot hp hp1 t.2 t.1)⁻¹ •
              fderiv ℂ (fun u : ℂ × CoeffPair p => canonicalDiscriminant hp (periodOnePotential u.2) u.1) t) t := by
  obtain ⟨W,V,hW,hV,hconn,hreal,hVW,hD,hroot,hglobal⟩ :=
    exists_sourceAbelian_almostReal_spectral_charts hp hp1
  refine ⟨W,V,hW,hV,hconn,hreal,hVW,?_,?_⟩
  · intro ψ hψ
    obtain ⟨D,hψD,hall⟩ := hglobal ψ hψ
    obtain ⟨E,_⟩ := hall ψ hψD
    exact ⟨E⟩
  · intro n
    constructor
    · intro t ht
      obtain ⟨D,hψD,hall⟩ := hglobal t.2 ht.1
      exact D.fullPrimitive_joint_analytic hall hD hroot n t ⟨hψD,ht.2⟩
    · intro t ht
      obtain ⟨D,hψD,hall⟩ := hglobal t.2 ht.1
      exact D.fullPrimitive_joint_hasFDerivAt hall hD hroot n t ⟨hψD,ht.2⟩

end NLS.ZakharovShabat
