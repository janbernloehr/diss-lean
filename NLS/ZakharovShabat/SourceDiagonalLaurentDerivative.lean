import NLS.ZakharovShabat.SourceDiagonalLaurentAtlas
import NLS.ZakharovShabat.SourceFullAbelianDifferential
import NLS.ZakharovShabat.SourceDiscriminantCotangent

/-! # Actual source derivatives of all integer Laurent action levels

Neighborhood independence transfers the checked full primitive differential
to each fixed-circle chart. Differentiation under that actual contour then
gives the weighted discriminant-variation integral, including level zero.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace SourceDiagonalLaurentLocalChart
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {φ : realDiagonalSourceLocus p}
variable (C : SourceDiagonalLaurentLocalChart hp hp1 φ)

theorem fullPrimitive_source_fderiv (n : ℤ) (ψ : realTypeSourceSubmodule p)
    (hψ : ψ.val ∈ ball φ.val C.radius) (z : ℂ)
    (hz : z ∈ sourceCanonicalRootDomain hp hp1 ψ.val) (v : CoeffPair p) :
    (fderiv ℂ (fun χ : CoeffPair p => sourceFullAbelianPrimitive hp hp1 C.ambient n (z,χ)) ψ.val) v =
      sourceDiscriminantCotangent hp z ψ.val v / sourceCanonicalRoot hp hp1 ψ.val z := by
  obtain ⟨W,V,_,hV,_,hreal,_,hcharts,hfull⟩ := exists_sourceFullAbelian_almostReal_differential hp hp1
  have he : (fun χ : CoeffPair p => sourceFullAbelianPrimitive hp hp1 C.ambient n (z,χ)) =ᶠ[𝓝 ψ.val]
      (fun χ => sourceFullAbelianPrimitive hp hp1 W n (z,χ)) := by
    have hc : Continuous (fun χ : CoeffPair p => (z,χ)) := continuous_const.prodMk continuous_id
    have ho := (C.root_domain_open.preimage hc).inter hV
    filter_upwards [ho.mem_nhds (show ψ.val ∈
      (fun χ : CoeffPair p => (z,χ)) ⁻¹' sourceCanonicalRootJointDomain hp hp1 (ball φ.val C.radius) ∩ V
        from ⟨⟨hψ,hz⟩,hreal ψ.property⟩)] with χ hχ
    obtain ⟨D⟩ := C.cauchy.charts χ (C.source_subset hχ.1.1)
    obtain ⟨E⟩ := hcharts χ hχ.2
    exact sourceFullAbelianPrimitive_independent_neighborhood D E n z
      (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 χ hχ.1.2)
  have hd := ((hfull n).2 (z,ψ.val) ⟨hreal ψ.property,hz⟩).comp ψ.val
    (hasFDerivAt_prodMk_right z ψ.val)
  change HasFDerivAt (fun χ : CoeffPair p => sourceFullAbelianPrimitive hp hp1 W n (z,χ)) _ _ at hd
  rw [he.fderiv_eq,hd.fderiv]
  have hΔ := fderiv_source_section_eq_joint
    (fun t : ℂ × CoeffPair p => canonicalDiscriminant hp (periodOnePotential t.2) t.1) z ψ.val
    ((analyticOnNhd_canonicalDiscriminant_periodOne hp hp1 (z,ψ.val) (mem_univ _)).differentiableAt)
  rw [sourceDiscriminantCotangent,hΔ]
  simp only [ContinuousLinearMap.comp_apply,smul_apply,smul_eq_mul,div_eq_inv_mul]

theorem fderiv_action (ψ : realTypeSourceSubmodule p) (hψ : ψ.val ∈ ball φ.val C.radius)
    (n k : ℤ) (hn : n ≠ 0) (v : CoeffPair p) :
    (fderiv ℂ (C.action n k) ψ.val) v = -(Real.pi : ℂ)⁻¹ *
      ∮ z in C(C.cauchy.discs.center n,C.contourRadius n),
        z^(k-1) * (sourceDiscriminantCotangent hp z ψ.val v / sourceCanonicalRoot hp hp1 ψ.val z) := by
  let D := sourceCanonicalRootJointDomain hp hp1 (ball φ.val C.radius) ∩
    {t : ℂ × CoeffPair p | t.1 ≠ 0}
  let F : ℂ × CoeffPair p → ℂ := fun t => t.1^(k-1)*sourceFullAbelianPrimitive hp hp1 C.ambient n t
  have hD : IsOpen D := C.root_domain_open.inter (isOpen_ne_fun continuous_fst continuous_const)
  have hF : AnalyticOnNhd ℂ F D := fun t ht =>
    (analyticAt_fst.zpow ht.2).mul (C.cauchy.full_analytic n t ⟨C.source_subset ht.1.1,ht.1.2⟩)
  have hcircle (z : ℂ) (hz : z ∈ sphere (C.cauchy.discs.center n) (C.contourRadius n)) :
      (z,ψ.val) ∈ D := by
    refine ⟨⟨hψ,C.cauchy.intermediate_circle_root n ψ.val (C.source_subset hψ) _
      (C.contourRadius_bounds n).1 (C.contourRadius_bounds n).2 z hz⟩,?_⟩
    intro he
    exact C.zero_not_mem_contour_disc n hn (he ▸ sphere_subset_closedBall hz)
  obtain ⟨U,hU,hψU,M,_,hbound⟩ := exists_uniform_joint_fderiv_bound_on_circle
    F D hD hF _ _ ψ.val hcircle
  have hdom (χ : CoeffPair p) (hχ : χ ∈ U) (θ : ℝ) :
      (circleMap (C.cauchy.discs.center n) (C.contourRadius n) θ,χ) ∈ D :=
    (hbound _ (circleMap_mem_sphere _ (C.contourRadius_pos n).le θ) χ hχ).1
  have hb (χ : CoeffPair p) (hχ : χ ∈ U) (θ : ℝ) :
      ‖fderiv ℂ F (circleMap (C.cauchy.discs.center n) (C.contourRadius n) θ,χ)‖ ≤ M :=
    (hbound _ (circleMap_mem_sphere _ (C.contourRadius_pos n).le θ) χ hχ).2
  have hi := differentiableAt_circleIntegral_of_jointAnalytic F D hD hF _ _
    (C.contourRadius_pos n).le U hU ψ.val hψU M hdom hb
  have hd := fderiv_circleIntegral_apply_of_jointAnalytic F D hD hF _ _
    (C.contourRadius_pos n).le U hU ψ.val hψU M hdom hb v
  change (fderiv ℂ (fun χ => -(Real.pi : ℂ)⁻¹ *
    ∮ z in C(C.cauchy.discs.center n,C.contourRadius n), F (z,χ)) ψ.val) v = _
  rw [fderiv_const_mul hi,smul_apply,smul_eq_mul,hd]
  congr 1
  apply circleIntegral.integral_congr (C.contourRadius_pos n).le
  intro z hz
  have hP := ((C.cauchy.full_analytic n (z,ψ.val)
    ⟨C.source_subset hψ,(hcircle z hz).1.2⟩).comp
      (f := fun χ : CoeffPair p => (z,χ)) (analyticAt_const.prod analyticAt_id)).differentiableAt
  change DifferentiableAt ℂ (fun χ : CoeffPair p => sourceFullAbelianPrimitive hp hp1 C.ambient n (z,χ)) ψ.val at hP
  dsimp only [F]
  rw [fderiv_const_mul hP,smul_apply,smul_eq_mul,
    C.fullPrimitive_source_fderiv n ψ hψ z (hcircle z hz).1.2 v]

end SourceDiagonalLaurentLocalChart

namespace SourceDiagonalLaurentAtlas
variable {hp : p ≠ ⊤} {hp1 : 1 < p} (A : SourceDiagonalLaurentAtlas hp hp1)

/-- One local contour family computes every integer-level derivative
at each real source in the atlas domain. -/
theorem fderiv_action_eq_local (ψ : realTypeSourceSubmodule p) (_hψ : ψ.val ∈ A.domain)
    (φ : realDiagonalSourceLocus p) (hφ : ψ.val ∈ A.sourceBall φ)
    (n k : ℤ) (hn : n ≠ 0) (v : CoeffPair p) :
    (fderiv ℂ (A.action n k) ψ.val) v =
      -(Real.pi : ℂ)⁻¹ * ∮ z in C((A.localChart φ).cauchy.discs.center n,(A.localChart φ).contourRadius n),
        z^(k-1) * (sourceDiscriminantCotangent hp z ψ.val v / sourceCanonicalRoot hp hp1 ψ.val z) := by
  have he : A.action n k =ᶠ[𝓝 ψ.val] (A.localChart φ).action n k := by
    filter_upwards [isOpen_ball.mem_nhds hφ] with χ hχ
    exact A.action_eq_local n k hn φ hχ
  rw [he.fderiv_eq]
  exact (A.localChart φ).fderiv_action ψ hφ n k hn v

end SourceDiagonalLaurentAtlas
end NLS.ZakharovShabat
