import NLS.ZakharovShabat.AppendixFCollapsedAnalytic
import NLS.ZakharovShabat.AppendixFSourceSpokes

/-!
# Collapsed-gap formulas on the original isolating discs

The Cauchy chart identifies the primitive at the collapsed point. Away
from it the original differential supplies the derivative. Thus the
path formula uses the original isolating disc, with no inclusion in
the auxiliary Cauchy disc required.
-/

noncomputable section
open Set Metric Filter Topology Complex MeasureTheory NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W S V : Set (CoeffPair p)}
variable {D : ℤ → Set ℂ} {c : ℝ}

/-- The collapsed primitive derivative holds throughout the whole omitted-gap domain. -/
theorem SourceFullAbelianUniformCauchyFamily.appendixF_collapsed_derivative_omitted
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (H : SourceLemma10_10Data hp hp1 S) (ψ : CoeffPair p) (hψS : ψ ∈ S)
    (hψC : ψ ∈ ball C.discs.source.val C.discs.sourceRadius) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0)
    (z : ℂ) (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ n) :
    HasDerivAt (fun w => sourceFullAbelianPrimitive hp hp1 W n (w,ψ))
      (-Complex.I*sourceActionChi hp hp1 n ψ z) z := by
  by_cases hzn : z ∈ sourcePeriodicSegment hp hp1 ψ n
  · exact C.appendixF_collapsed_primitive_hasDerivAt H ψ hψS hψC n hgap z
      (ball_subset_closedBall (C.segment_subset_outer n ψ hψC hzn))
  · have hroot : z ∈ sourceCanonicalRootDomain hp hp1 ψ := by
      intro m
      by_cases hm : m = n
      · subst m; exact hzn
      · exact hz m hm
    obtain ⟨E⟩ := C.charts ψ hψC
    rw [← H.appendixF_collapsed_differential ψ hψS n hgap z hroot]
    exact sourceFullAbelianPrimitive_hasDerivAt E n z hroot

/-- Any C1 path in the original closed disc computes the collapsed endpoint average. -/
theorem SourceFullAbelianUniformCauchyFamily.appendixF_collapsed_original_path
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (H : SourceLemma10_10Data hp hp1 S) (hVS : V ⊆ S)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψV : ψ ∈ V)
    (hψC : ψ ∈ ball C.discs.source.val C.discs.sourceRadius) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0)
    (ν : ℂ) (hν : ν ∈ sourceCanonicalRootDomain hp hp1 ψ)
    (γ : Path (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) ν)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hpath : ∀ t ∈ Icc (0:ℝ) 1, γ.extend t ∈ closure (D n)) :
    CurveIntegrable (holomorphicOneForm (fun z => -Complex.I*sourceActionChi hp hp1 n ψ z)) γ ∧
      sourceAbelianEndpointAverage hp hp1 n ν ψ =
        ∫ᶜ z in γ, holomorphicOneForm (fun w => -Complex.I*sourceActionChi hp hp1 n ψ w) z := by
  have hcont : ContinuousOn (fun z => -Complex.I*sourceActionChi hp hp1 n ψ z) (closure (D n)) :=
    ((C.extension_analytic ψ hψC n).continuousOn.mono (hD.closedDisk_subset_omittedDomain ψ hψV n)).congr
      (fun z hz => (sourceCriticalRootRatioExtension_eq_neg_I_chi hp hp1 ψ n z
        (hD.closedDisk_subset_omittedDomain ψ hψV n hz)).symm)
  have hω : ContinuousOn (holomorphicOneForm (fun z => -Complex.I*sourceActionChi hp hp1 n ψ z))
      (closure (D n)) := hcont.smul continuousOn_const
  have hint : CurveIntegrable (holomorphicOneForm (fun z => -Complex.I*sourceActionChi hp hp1 n ψ z)) γ :=
    hω.curveIntegrable_of_contDiffOn hγ
      (fun t => by simpa only [Path.extend_apply _ t.property] using hpath t t.property)
  refine ⟨hint,?_⟩
  have hFTC := curveIntegral_eq_sub_of_primitive
    (fun z => -Complex.I*sourceActionChi hp hp1 n ψ z)
    (fun z => sourceFullAbelianPrimitive hp hp1 W n (z,ψ)) (closure (D n))
    (fun z hz => C.appendixF_collapsed_derivative_omitted H ψ (hVS hψV) hψC n hgap z
      (hD.closedDisk_subset_omittedDomain ψ hψV n hz)) γ hγ hpath hint
  have hrl := sub_eq_zero.mp hgap
  have hmid : canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n =
      canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n := by
    dsimp only [canonicalPeriodicMidpoint]
    rw [hrl]
    ring
  rw [C.fullPrimitive_collapsed_endpoint_value n n ψ hψC hgap
    (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
    (by simp only [hmid,mem_insert_iff,true_or])] at hFTC
  simpa only [sub_self,mul_zero,sub_zero,C.endpointAverage_eq ψ hψC n ν hν] using hFTC.symm

/-- The original-disc segment formula retains the full displacement coefficient. -/
theorem SourceFullAbelianUniformCauchyFamily.appendixF_collapsed_original_segment
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (H : SourceLemma10_10Data hp hp1 S) (hVS : V ⊆ S)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψV : ψ ∈ V)
    (hψC : ψ ∈ ball C.discs.source.val C.discs.sourceRadius) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0)
    (ν : ℂ) (hν : ν ∈ sourceCanonicalRootDomain hp hp1 ψ) (hνD : ν ∈ closure (D n)) :
    let τ := canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
    sourceAbelianEndpointAverage hp hp1 n ν ψ =
      -Complex.I*(ν-τ)*∫ t in (0:ℝ)..1, sourceActionChi hp hp1 n ψ (τ+(t:ℂ)*(ν-τ)) := by
  dsimp only
  let τ := canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  obtain ⟨a,R,hR,he⟩ := hD.discs n
  have hτ : τ ∈ closure (D n) := subset_closure
    (hD.gap ψ hψV n (sourcePeriodicMidpoint_mem_segment hp hp1 ψ n))
  have hconv : Convex ℝ (closure (D n)) := by
    rw [he,closure_ball _ hR.ne']
    exact convex_closedBall _ _
  have hpath (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : (Path.segment τ ν).extend t ∈ closure (D n) := by
    rw [(Path.eqOn_extend_segment τ ν) ht]
    exact hconv.lineMap_mem hτ hνD ht
  have h := (C.appendixF_collapsed_original_path H hVS hD ψ hψV hψC n hgap ν hν
    (Path.segment τ ν) (contDiffOn_segment_extend τ ν) hpath).2
  rw [curveIntegral_segment] at h
  simp only [holomorphicOneForm_apply,AffineMap.lineMap_apply_module',Complex.real_smul] at h
  simp only [intervalIntegral.integral_const_mul,intervalIntegral.integral_mul_const] at h
  simpa only [mul_assoc,mul_left_comm,mul_comm,add_comm] using h

/-- The regular collapsed formula is analytic on the original source neighborhood. -/
theorem SourceCorollary10_6Data.appendixF_original_chi_integral_analytic
    (H : SourceCorollary10_6Data hp hp1 S) (hS : IsOpen S)
    (hV : IsOpen V) (hVS : V ⊆ S)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (n : ℤ)
    (ν : ℂ) (hνD : ν ∈ closure (D n)) :
    let τ := fun ψ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n
    AnalyticOnNhd ℂ (fun ψ => -Complex.I*(ν-τ ψ)*∫ t in (0:ℝ)..1,
      sourceActionChi hp hp1 n ψ (τ ψ+(t:ℂ)*(ν-τ ψ))) V := by
  dsimp only
  let τ := fun ψ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let Z : ℂ × CoeffPair p → ℂ := fun q => τ q.2+q.1*(ν-τ q.2)
  let G : ℂ × CoeffPair p → ℂ := fun q => sourceActionChi hp hp1 n q.2 (Z q)
  have hτ : AnalyticOnNhd ℂ τ V := (H.roots.roots.symmetric.midpoint n).mono hVS
  obtain ⟨a,R,hR,he⟩ := hD.discs n
  have hconv : Convex ℝ (closure (D n)) := by
    rw [he,closure_ball _ hR.ne']
    exact convex_closedBall _ _
  have hGA (ψ : CoeffPair p) (hψ : ψ ∈ V)
      (t : ℝ) (ht : t ∈ uIcc (0:ℝ) 1) : AnalyticAt ℂ G ((t:ℂ),ψ) := by
    have hτD : τ ψ ∈ closure (D n) := subset_closure
      (hD.gap ψ hψ n (sourcePeriodicMidpoint_mem_segment hp hp1 ψ n))
    have hZD : Z ((t:ℂ),ψ) ∈ closure (D n) := by
      have h := hconv.lineMap_mem hτD hνD
        (show t ∈ Icc (0:ℝ) 1 by simpa only [uIcc_of_le zero_le_one] using ht)
      simpa only [Z,AffineMap.lineMap_apply_module',Complex.real_smul,add_comm] using h
    have hAτ : AnalyticAt ℂ (fun q : ℂ × CoeffPair p => τ q.2) ((t:ℂ),ψ) :=
      (hτ ψ hψ).comp (g := τ) (f := fun q : ℂ × CoeffPair p => q.2)
        (show AnalyticAt ℂ (fun q : ℂ × CoeffPair p => q.2) ((t:ℂ),ψ) from analyticAt_snd)
    have hAZ : AnalyticAt ℂ Z ((t:ℂ),ψ) :=
      hAτ.add (analyticAt_fst.mul (analyticAt_const.sub hAτ))
    exact (H.chi_joint hS n (Z ((t:ℂ),ψ),ψ)
      ⟨hVS hψ,hD.closedDisk_subset_omittedDomain ψ hψ n hZD⟩).comp
        (f := fun q : ℂ × CoeffPair p => (Z q,q.2)) (hAZ.prod analyticAt_snd)
  have hI := analyticOnNhd_intervalIntegral_of_jointAnalytic G
    (D := {q | AnalyticAt ℂ G q}) (isOpen_analyticAt ℂ G) (fun _ hq => hq) 0 1 hV hGA
  exact (analyticOnNhd_const.mul (analyticOnNhd_const.sub hτ)).mul hI

/-- A cover by source Cauchy charts identifies the analytic extension on the unchanged V.
The auxiliary chart may depend on the source, while the original disc and terminal point stay fixed. -/
theorem SourceLemma10_10Data.appendixF_original_collapsed_analytic_extension
    (H : SourceLemma10_10Data hp hp1 S) (hS : IsOpen S)
    (hV : IsOpen V) (hVS : V ⊆ S)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (hcharts : ∀ ψ ∈ V, ∃ C : SourceFullAbelianUniformCauchyFamily hp hp1 W,
      ψ ∈ ball C.discs.source.val C.discs.sourceRadius)
    (n : ℤ) (ν : ℂ) (hν : ν ∈ frontier (D n)) :
    ∃ G : CoeffPair p → ℂ, AnalyticOnNhd ℂ G V ∧
      ∀ ψ ∈ V, canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0 →
        G ψ = sourceAbelianEndpointAverage hp hp1 n ν ψ := by
  let τ := fun ψ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  refine ⟨fun ψ => -Complex.I*(ν-τ ψ)*∫ t in (0:ℝ)..1,
    sourceActionChi hp hp1 n ψ (τ ψ+(t:ℂ)*(ν-τ ψ)),
    H.previous.previous.previous.appendixF_original_chi_integral_analytic hS hV hVS hD n ν
      (frontier_subset_closure hν),?_⟩
  intro ψ hψ hgap
  obtain ⟨C,hψC⟩ := hcharts ψ hψ
  have hopen : IsOpen (D n) := by
    obtain ⟨a,R,_,he⟩ := hD.discs n
    rw [he]
    exact isOpen_ball
  have hνnot : ν ∉ D n := by
    simpa only [hopen.interior_eq] using hν.2
  have hroot : ν ∈ sourceCanonicalRootDomain hp hp1 ψ :=
    hD.closedCutDisk_subset_rootDomain ψ hψ n
      ⟨frontier_subset_closure hν,fun hs => hνnot (hD.gap ψ hψ n hs)⟩
  exact (C.appendixF_collapsed_original_segment H hVS hD ψ hψ hψC n hgap ν hroot
    (frontier_subset_closure hν)).symm

end NLS.ZakharovShabat
