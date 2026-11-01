import NLS.ZakharovShabat.SourceAbelianEndpointIntegrals
import NLS.ZakharovShabat.SourceActionChi
import NLS.ZakharovShabat.SourceLemma10_10

/-!
# The actual collapsed-gap path formula in Appendix F

The derivative of the filled canonical primitive is the literal deleted
product multiplied by -i throughout the closed isolating disc. Consequently
the improper endpoint definition equals the regular integral along every
C1 path in that disc, including paths through the collapsed point.
-/

noncomputable section
open Set Metric Filter Topology Complex MeasureTheory NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- At a collapsed gap the selected critical factor cancels, retaining -i. -/
theorem SourceLemma10_10Data.appendixF_collapsed_differential
    {hp : p ≠ ⊤} {hp1 : 1 < p} {S : Set (CoeffPair p)}
    (H : SourceLemma10_10Data hp hp1 S) (ψ : CoeffPair p) (hψ : ψ ∈ S)
    (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n = 0)
    (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    sourceAbelianDifferential hp hp1 ψ z = -Complex.I * sourceActionChi hp hp1 n ψ z := by
  have hcrit := H.critical_eq_midpoint_of_gap_zero ψ hψ n
    (by simpa only [sourcePeriodicGapDisplacement_apply] using hgap)
  have hne := sourceStandardRoot_ne_zero_off_segment hp hp1 ψ n z (hz n)
  rw [sourceStandardRoot_of_zeroGap hp hp1 ψ n z hgap] at hne
  rw [sourceAbelianDifferential,
    sourceCriticalRootRatio_eq_selectedFactor_mul_chi hp hp1 ψ n z hz,
    hcrit, sourceStandardRoot_of_zeroGap hp hp1 ψ n z hgap, div_self hne, mul_one]

namespace SourceFullAbelianUniformCauchyFamily
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W S : Set (CoeffPair p)}
variable (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)

/-- The actual filled primitive has derivative -i χ_n even at the collapsed point. -/
theorem appendixF_collapsed_primitive_hasDerivAt
    (H : SourceLemma10_10Data hp hp1 S) (ψ : CoeffPair p) (hψS : ψ ∈ S)
    (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n = 0)
    (z : ℂ) (hz : z ∈ closedBall (C.discs.center n) (C.discs.outer n)) :
    HasDerivAt (fun w => sourceFullAbelianPrimitive hp hp1 W n (w,ψ))
      (-Complex.I * sourceActionChi hp hp1 n ψ z) z := by
  obtain ⟨E⟩ := C.charts ψ hψ
  have hoff (w : ℂ) (hw : w ∈ sourceCanonicalRootDomain hp hp1 ψ) :
      HasDerivAt (fun v => sourceFullAbelianPrimitive hp hp1 W n (v,ψ))
        (-Complex.I * sourceActionChi hp hp1 n ψ w) w := by
    rw [← H.appendixF_collapsed_differential ψ hψS n hgap w hw]
    exact sourceFullAbelianPrimitive_hasDerivAt E n w hw
  by_cases hzB : z ∈ ball (C.discs.center n) (C.discs.outer n)
  · let F : ℂ → ℂ := fun w => sourceFullAbelianPrimitive hp hp1 W n (w,ψ)
    let g := sourceCriticalRootRatioExtension hp hp1 n ψ
    have hF : AnalyticOnNhd ℂ F (ball (C.discs.center n) (C.discs.outer n)) :=
      (sourceFullAbelianPrimitive_spectral_analytic E n).mono
        (C.ball_subset_openGapComplement_of_collapsed n ψ hψ hgap)
    have hg : AnalyticOnNhd ℂ g (ball (C.discs.center n) (C.discs.outer n)) :=
      (C.extension_analytic ψ hψ n).mono
        (ball_subset_closedBall.trans (C.discs.avoids_other ψ hψ n))
    have heq : EqOn (deriv F) g
        (ball (C.discs.center n) (C.discs.outer n) \ sourcePeriodicSegment hp hp1 ψ n) := by
      intro w hw
      have hroot := sourceAbelian_discComplement_subset_rootDomain hp hp1 ψ n
        (C.discs.center n) (C.discs.outer n) (C.discs.avoids_other ψ hψ n) hw
      exact (hoff w hroot).deriv.trans
        (sourceCriticalRootRatioExtension_eq_neg_I_chi hp hp1 ψ n w
          (fun m _ => hroot m)).symm
    have hdense := dense_complex_segment_complement
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
    have heqB := heq.of_subset_closure hF.deriv.continuousOn
      hg.continuousOn sdiff_subset (hdense.open_subset_closure_inter isOpen_ball)
    have hder := (hF z hzB).differentiableAt.hasDerivAt
    rw [heqB hzB] at hder
    change HasDerivAt F (sourceCriticalRootRatioExtension hp hp1 n ψ z) z at hder
    rw [sourceCriticalRootRatioExtension_eq_neg_I_chi hp hp1 ψ n z
      (C.discs.avoids_other ψ hψ n hz)] at hder
    exact hder
  · exact hoff z (C.circle_root n ψ hψ z
      (mem_sphere.mpr (le_antisymm (mem_closedBall.mp hz) (not_lt.mp hzB))))

/-- Every C1 path in the closed disc computes the actual improper endpoint integral.
The path may pass through the collapsed point, where the integrand is regular. -/
theorem appendixF_collapsed_endpoint_path
    (H : SourceLemma10_10Data hp hp1 S) (ψ : CoeffPair p) (hψS : ψ ∈ S)
    (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n = 0)
    (a ν : ℂ)
    (ha : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Set ℂ))
    (hν : ν ∈ sourceCanonicalRootDomain hp hp1 ψ) (γ : Path a ν)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hpath : ∀ t ∈ Icc (0:ℝ) 1,
      γ.extend t ∈ closedBall (C.discs.center n) (C.discs.outer n)) :
    CurveIntegrable (holomorphicOneForm (fun z => -Complex.I * sourceActionChi hp hp1 n ψ z)) γ ∧
      sourceAbelianEndpointIntegral hp hp1 ψ a ν =
        ∫ᶜ z in γ, holomorphicOneForm (fun w => -Complex.I * sourceActionChi hp hp1 n ψ w) z := by
  have hcont : ContinuousOn (fun z => -Complex.I * sourceActionChi hp hp1 n ψ z)
      (closedBall (C.discs.center n) (C.discs.outer n)) :=
    ((C.extension_analytic ψ hψ n).continuousOn.mono (C.discs.avoids_other ψ hψ n)).congr
      (fun z hz => (sourceCriticalRootRatioExtension_eq_neg_I_chi hp hp1 ψ n z
        (C.discs.avoids_other ψ hψ n hz)).symm)
  have hω : ContinuousOn (holomorphicOneForm (fun z => -Complex.I * sourceActionChi hp hp1 n ψ z))
      (closedBall (C.discs.center n) (C.discs.outer n)) := hcont.smul continuousOn_const
  have hint := hω.curveIntegrable_of_contDiffOn hγ
    (fun t => by simpa only [Path.extend_apply _ t.property] using hpath t t.property)
  refine ⟨hint,?_⟩
  have hFTC := curveIntegral_eq_sub_of_primitive
    (fun z => -Complex.I * sourceActionChi hp hp1 n ψ z)
    (fun z => sourceFullAbelianPrimitive hp hp1 W n (z,ψ))
    (closedBall (C.discs.center n) (C.discs.outer n))
    (C.appendixF_collapsed_primitive_hasDerivAt H ψ hψS hψ n hgap) γ hγ hpath hint
  rw [C.fullPrimitive_collapsed_endpoint_value n n ψ hψ hgap a ha] at hFTC
  simpa only [sub_self,mul_zero,sub_zero,C.endpointIntegral_eq ψ hψ n a ν ha hν] using hFTC.symm

/-- The literal endpoint average has the printed -i χ_n path formula.
No avoidance condition at the collapsed midpoint is required. -/
theorem appendixF_collapsed_average_path
    (H : SourceLemma10_10Data hp hp1 S) (ψ : CoeffPair p) (hψS : ψ ∈ S)
    (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n = 0)
    (ν : ℂ) (hν : ν ∈ sourceCanonicalRootDomain hp hp1 ψ)
    (γ : Path (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n) ν)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hpath : ∀ t ∈ Icc (0:ℝ) 1,
      γ.extend t ∈ closedBall (C.discs.center n) (C.discs.outer n)) :
    CurveIntegrable (holomorphicOneForm (sourceActionChi hp hp1 n ψ)) γ ∧
      sourceAbelianEndpointAverage hp hp1 n ν ψ =
        -Complex.I * ∫ᶜ z in γ, holomorphicOneForm (sourceActionChi hp hp1 n ψ) z := by
  have hrl := sub_eq_zero.mp hgap
  have hmid : canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n =
      canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n := by
    dsimp only [canonicalPeriodicMidpoint]
    rw [hrl]
    ring
  have ha : canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n ∈
      ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} : Set ℂ) := by
    simp only [hmid,mem_insert_iff,true_or]
  have hform : holomorphicOneForm (fun z => -Complex.I * sourceActionChi hp hp1 n ψ z) =
      -Complex.I • holomorphicOneForm (sourceActionChi hp hp1 n ψ) := by
    ext z
    simp only [Pi.smul_apply,smul_apply,holomorphicOneForm_apply,smul_eq_mul]
    ring
  obtain ⟨hint,heq⟩ := C.appendixF_collapsed_endpoint_path H ψ hψS hψ n hgap _ ν ha hν γ hγ hpath
  rw [hform,curveIntegrable_smul_iff] at hint
  rw [hform,curveIntegral_smul,smul_eq_mul,C.endpointIntegral_eq ψ hψ n _ ν ha hν,
    ← C.endpointAverage_eq ψ hψ n ν hν] at heq
  exact ⟨hint.resolve_left (neg_ne_zero.mpr Complex.I_ne_zero),heq⟩

/-- The regular segment formula uses the exact displacement ν-τ_n. -/
theorem appendixF_collapsed_average_segment
    (H : SourceLemma10_10Data hp hp1 S) (ψ : CoeffPair p) (hψS : ψ ∈ S)
    (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n = 0)
    (ν : ℂ) (hν : ν ∈ sourceCanonicalRootDomain hp hp1 ψ)
    (hνD : ν ∈ closedBall (C.discs.center n) (C.discs.outer n)) :
    let τ := canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
    sourceAbelianEndpointAverage hp hp1 n ν ψ =
      -Complex.I * (ν-τ) * ∫ t in (0:ℝ)..1,
        sourceActionChi hp hp1 n ψ (τ+(t:ℂ)*(ν-τ)) := by
  dsimp only
  let τ := canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  have hτD : τ ∈ closedBall (C.discs.center n) (C.discs.outer n) :=
    ball_subset_closedBall (C.segment_subset_outer n ψ hψ
      (sourcePeriodicMidpoint_mem_segment hp hp1 ψ n))
  have hpath (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      (Path.segment τ ν).extend t ∈ closedBall (C.discs.center n) (C.discs.outer n) := by
    rw [(Path.eqOn_extend_segment τ ν) ht]
    exact (convex_closedBall (C.discs.center n) (C.discs.outer n)).lineMap_mem hτD hνD ht
  have heq := (C.appendixF_collapsed_average_path H ψ hψS hψ n hgap ν hν
    (Path.segment τ ν) (contDiffOn_segment_extend τ ν) hpath).2
  rw [curveIntegral_segment] at heq
  simp only [holomorphicOneForm_apply,AffineMap.lineMap_apply_module',Complex.real_smul] at heq
  rw [intervalIntegral.integral_mul_const] at heq
  simpa only [mul_assoc,mul_left_comm,mul_comm,add_comm] using heq

end SourceFullAbelianUniformCauchyFamily
end NLS.ZakharovShabat
