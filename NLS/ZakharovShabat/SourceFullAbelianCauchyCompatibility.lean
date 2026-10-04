import NLS.ZakharovShabat.SourceFullAbelianDifferential
import NLS.ZakharovShabat.SourceAbelianContinuedProperties

/-! # The full primitive agrees with normalized Cauchy charts

The real projection path identifies the two logarithms at a fixed collar
anchor. Spectral connectedness then identifies them on the entire cut disc,
transferring the exact endpoint constants to the full canonical function.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceAbelianUniformDiscFamily
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
variable (D : SourceAbelianUniformDiscFamily hp hp1 W)
variable (hall : ∀ χ ∈ ball D.source.val D.sourceRadius,
  ∃ E : SourceAbelianSpectralChart hp hp1 W χ, E.discs = D)
variable (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
variable (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
include hall hD hroot

/-- Exact agreement on every overlapping normalized cut disc. -/
theorem fullPrimitive_eq_cauchy (C : SourceAbelianDiscJointChart hp hp1 W)
    (n : ℤ) (ψ : CoeffPair p) (hψD : ψ ∈ ball D.source.val D.sourceRadius)
    (hψC : ψ ∈ ball C.source.val C.sourceRadius) :
    EqOn (fun z => sourceFullAbelianPrimitive hp hp1 W n (z,ψ)) (fun z => C.toFun n (z,ψ))
      (ball C.cauchy.center C.cauchy.radius \ sourcePeriodicSegment hp hp1 ψ C.gap) := by
  let a := C.cauchy.anchor
  let L : ℝ → ℂ × CoeffPair p := fun s => (a,sourceRealProjectionPath hp ψ s)
  have hL : Continuous L := by dsimp [L,sourceRealProjectionPath]; fun_prop
  have hpathC (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : L s ∈ C.domain := by
    have hb := C.projectionPath_mem_ball ψ hψC s hs
    exact (C.mem_domain_iff (L s)).mpr ⟨C.cauchy.anchor_mem.1,hb,
      C.cauchy.anchor_off_segment _ (C.source_subset hb).1⟩
  have hpathD (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      L s ∈ sourceCanonicalRootJointDomain hp hp1 (ball D.source.val D.sourceRadius) :=
    ⟨D.projectionPath_mem_ball ψ hψD s hs,(hpathC s hs).2.2⟩
  have heq := continuousLogarithms_eqOn
    (fun s => sourceFullAbelianPrimitive hp hp1 W n (L s)) (fun s => C.toFun n (L s))
    (Icc (0:ℝ) 1) isPreconnected_Icc
    ((D.fullPrimitive_joint_analytic hall hD hroot n).continuousOn.comp hL.continuousOn hpathD)
    ((C.analytic n).continuousOn.comp hL.continuousOn hpathC)
    (fun s hs => by
      obtain ⟨E,_⟩ := hall (L s).2 (hpathD s hs).1
      exact (sourceFullAbelianPrimitive_exp E hroot n (L s).1 (hpathD s hs).2).trans
        (C.exp_toFun hD hroot n (L s) (hpathC s hs)).symm)
    0 (by simp) (by
      have h0D := hpathD 0 (by simp)
      have h0C := hpathC 0 (by simp)
      simp only [L,sourceRealProjectionPath_zero] at h0D h0C ⊢
      obtain ⟨E,_⟩ := hall (sourceRealTypeProjection hp ψ).val h0D.1
      exact (sourceFullAbelianPrimitive_eq_real (sourceRealTypeProjection hp ψ) E n a
        (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 _ h0D.2)).trans
        (C.real_eq n (sourceRealTypeProjection hp ψ) a h0C).symm)
  have haeq : sourceFullAbelianPrimitive hp hp1 W n (a,ψ) = C.toFun n (a,ψ) := by
    simpa only [L,sourceRealProjectionPath_one] using heq (show (1:ℝ) ∈ Icc 0 1 by simp)
  let U := ball C.cauchy.center C.cauchy.radius \ sourcePeriodicSegment hp hp1 ψ C.gap
  have ha : a ∈ U := ⟨C.cauchy.anchor_mem.1,C.cauchy.anchor_off_segment ψ (C.source_subset hψC).1⟩
  have hU (z : ℂ) (hz : z ∈ U) : (z,ψ) ∈ C.domain := (C.mem_domain_iff (z,ψ)).mpr ⟨hz.1,hψC,hz.2⟩
  obtain ⟨E,_⟩ := hall ψ hψD
  apply continuousLogarithms_eqOn _ _ U
    (isConnected_sourceAbelian_complexDisc hp hp1 ψ C.gap C.cauchy.center C.cauchy.radius
      (C.cauchy.segment_subset_outer ψ (C.source_subset hψC).1)).isPreconnected
    ((sourceFullAbelianPrimitive_spectral_analytic E n).continuousOn.mono
      (fun z hz => sourceCanonicalRootDomain_subset_openGapComplement hp hp1 ψ (hU z hz).2.2))
    ((C.analytic n).continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn hU)
    (fun z hz => (sourceFullAbelianPrimitive_exp E hroot n z (hU z hz).2.2).trans
      (C.exp_toFun hD hroot n (z,ψ) (hU z hz)).symm) a ha haeq

/-- The canonical full function inherits the exact limits at both
endpoints, including a collapsed selected gap. -/
theorem fullPrimitive_endpoint_limit (C : SourceAbelianDiscJointChart hp hp1 W)
    (n : ℤ) (ψ : CoeffPair p) (hψD : ψ ∈ ball D.source.val D.sourceRadius)
    (hψC : ψ ∈ ball C.source.val C.sourceRadius) (a : ℂ)
    (ha : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) C.gap,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) C.gap} : Set ℂ)) :
    Tendsto (fun z => sourceFullAbelianPrimitive hp hp1 W n (z,ψ))
      (𝓝[ball C.cauchy.center C.cauchy.radius \ sourcePeriodicSegment hp hp1 ψ C.gap] a)
      (𝓝 (I*(Real.pi : ℂ)*(n-C.gap))) := by
  have heq := D.fullPrimitive_eq_cauchy hall hD hroot C n ψ hψD hψC
  have hlim := C.cauchy.primitive_endpoint_limit n ψ (C.source_subset hψC).1 a ha
  exact hlim.congr' (Filter.eventuallyEq_of_mem self_mem_nhdsWithin (fun z hz => (heq hz).symm))

end NLS.ZakharovShabat.SourceAbelianUniformDiscFamily

namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every real source and selected gap has a complex source neighborhood
on which the canonical full primitive has both exact endpoint limits.
The radius in this theorem may depend on the selected gap. -/
theorem exists_sourceFullAbelian_endpoint_neighborhood (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (j : ℤ) :
    ∃ (W : Set (CoeffPair p)) (C : SourceAbelianDiscJointChart hp hp1 W) (r : ℝ),
      C.source = φ ∧ C.gap = j ∧ 0 < r ∧ ball φ.val r ⊆ W ∧
      ∀ ψ ∈ ball φ.val r, Nonempty (SourceAbelianSpectralChart hp hp1 W ψ) ∧
        ∀ (n : ℤ) (a : ℂ),
          a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j,
            canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j} : Set ℂ) →
          Tendsto (fun z => sourceFullAbelianPrimitive hp hp1 W n (z,ψ))
            (𝓝[ball C.cauchy.center C.cauchy.radius \ sourcePeriodicSegment hp hp1 ψ j] a)
            (𝓝 (I*(Real.pi : ℂ)*(n-j))) := by
  obtain ⟨W,V,hW,_,_,hreal,hVW,hD,hroot,hglobal⟩ :=
    exists_sourceAbelian_almostReal_spectral_charts hp hp1
  obtain ⟨D,hφD,hall⟩ := hglobal φ.val (hreal φ.property)
  obtain ⟨C,hCφ,hCj⟩ := exists_sourceAbelianDiscJointChart hp hp1 W hW φ (hVW (hreal φ.property)) j
  have hφC : φ.val ∈ ball C.source.val C.sourceRadius := by
    rw [hCφ]
    exact mem_ball_self C.sourceRadius_pos
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp ((isOpen_ball.inter isOpen_ball).mem_nhds ⟨hφD,hφC⟩)
  refine ⟨W,C,r,hCφ,hCj,hr,fun ψ hψ => D.source_subset (hsub hψ).1,?_⟩
  intro ψ hψ
  obtain ⟨E,_⟩ := hall ψ (hsub hψ).1
  refine ⟨⟨E⟩,?_⟩
  intro n a ha
  have haC : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) C.gap,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) C.gap} : Set ℂ) := by
    simpa only [hCj] using ha
  simpa only [hCj] using D.fullPrimitive_endpoint_limit hall hD hroot C n ψ
    (hsub hψ).1 (hsub hψ).2 a haC

end NLS.ZakharovShabat
