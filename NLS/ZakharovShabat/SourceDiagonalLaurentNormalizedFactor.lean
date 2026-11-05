import NLS.ZakharovShabat.SourceLaurentSquaredGapFactor
import NLS.ZakharovShabat.SourceDiagonalLaurentCompatibility
import NLS.ZakharovShabat.SourceNormalizedActionRootAnalytic
import NLS.ZakharovShabat.SourceOpenGapDensity
import NLS.ZakharovShabat.SourceRealActionLocalOverlap

/-! # Analytic Laurent factors through collapsed diagonal gaps

Every local diagonal Laurent chart has analytic squared-gap factors on a
complex source neighborhood. The ordinary factor is identified with the
existing independently normalized NLS action, including at closed gaps,
by real open-gap density and the real-form identity principle.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceDiagonalLaurentLocalChart
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {φ : realDiagonalSourceLocus p}

def normalizedAction (C : SourceDiagonalLaurentLocalChart hp hp1 φ)
    (n k : ℤ) : CoeffPair p → ℂ :=
  C.cauchy.laurentSquaredGapCircle n k (C.contourRadius n)

theorem action_eq_squaredGap_mul_normalizedAction
    (C : SourceDiagonalLaurentLocalChart hp hp1 φ) (n k : ℤ) (hn : n ≠ 0)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball φ.val C.radius) :
    C.action n k ψ =
      (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2 *
        C.normalizedAction n k ψ :=
  C.cauchy.laurentPrimitiveCircle_eq_squaredGap_mul n k ψ (C.source_subset hψ) _
    (C.contourRadius_bounds n).1 (C.contourRadius_bounds n).2 (C.zero_not_mem_contour_disc n hn)

/-- One neighborhood supports all integer levels of a selected noncentral gap. -/
theorem exists_normalizedAction_analytic
    (C : SourceDiagonalLaurentLocalChart hp hp1 φ) (n : ℤ) (hn : n ≠ 0) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ.val ∈ U ∧ U ⊆ ball φ.val C.radius ∧
      ∀ k : ℤ, AnalyticOnNhd ℂ (C.normalizedAction n k) U := by
  obtain ⟨G,hG,_,hreal,hdata⟩ := exists_global_source_analytic_midpoint_squaredGap hp hp1
  let U := ball φ.val C.radius ∩ G
  have hroot : IsOpen (sourceCanonicalRootJointDomain hp hp1 U) := by
    have he : sourceCanonicalRootJointDomain hp hp1 U =
        sourceCanonicalRootJointDomain hp hp1 (ball φ.val C.radius) ∩ Prod.snd ⁻¹' G := by
      ext t
      exact ⟨fun ht => ⟨⟨ht.1.1,ht.2⟩,ht.1.2⟩,fun ht => ⟨⟨ht.1.1,ht.2⟩,ht.1.2⟩⟩
    rw [he]
    exact C.root_domain_open.inter (hG.preimage continuous_snd)
  refine ⟨U,isOpen_ball.inter hG,⟨mem_ball_self C.radius_pos,hreal φ.property.1⟩,inter_subset_left,?_⟩
  intro k
  exact C.cauchy.laurentSquaredGapCircle_analytic n k _
    (C.contourRadius_bounds n).1 (C.contourRadius_bounds n).2 (C.zero_not_mem_contour_disc n hn)
    U (isOpen_ball.inter hG) (fun _ hψ => C.source_subset hψ.1) hroot
    (fun ψ hψ => (hdata ψ hψ.2 n).1) (fun ψ hψ => (hdata ψ hψ.2 n).2)

/-- The level-one local contour agrees with the ordinary NLS action at real sources. -/
theorem action_one_eq_sourceComplexAction_real
    (C : SourceDiagonalLaurentLocalChart hp hp1 φ)
    (ψ : realTypeSourceSubmodule p) (hψ : ψ.val ∈ ball φ.val C.radius)
    (n : ℤ) (hn : n ≠ 0) :
    C.action n 1 ψ.val = sourceComplexAction hp hp1 n ψ.val := by
  rw [C.action_eq_real ψ hψ n 1 hn,
    show (1 : ℤ) = (0 : ℕ)+1 by norm_num,sourceRealLaurentAction_nat,
    sourceRealHigherAction_zero,sourceComplexAction_eq_sourceRealAction hp hp1 n ψ.val ψ.property]
  exact Complex.ext (by simp) (by
    simp only [ofReal_im]
    exact (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero hp hp1 ψ.val ψ.property n).2.1.symm)

/-- Open-gap cancellation and real density identify the ordinary factor
also at a collapsed gap. Holomorphic uniqueness then identifies complex germs. -/
theorem exists_normalizedAction_one_eq
    (C : SourceDiagonalLaurentLocalChart hp hp1 φ) (n : ℤ) (hn : n ≠ 0) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ.val ∈ U ∧ U ⊆ ball φ.val C.radius ∧
      (∀ k : ℤ, AnalyticOnNhd ℂ (C.normalizedAction n k) U) ∧
      EqOn (C.normalizedAction n 1) (sourceNormalizedActionComplexExtension hp hp1 n) U := by
  obtain ⟨A,hA,hφA,hAC,hAn⟩ := C.exists_normalizedAction_analytic n hn
  obtain ⟨B,hB,hφB,hBn,hfactor⟩ := exists_local_sourceNormalizedAction_analytic_factor hp hp1 φ.val φ.property.1 n
  let V := A ∩ B
  have hV : IsOpen V := hA.inter hB
  have hF : AnalyticOnNhd ℂ (C.normalizedAction n 1) V := (hAn 1).mono inter_subset_left
  have hG : AnalyticOnNhd ℂ (sourceNormalizedActionComplexExtension hp hp1 n) V := hBn.mono inter_subset_right
  have hreal (ψ : CoeffPair p) (hψ : ψ ∈ V) (hψr : IsRealType (CoeffPair.toMax p ψ)) :
      C.normalizedAction n 1 ψ = sourceNormalizedActionComplexExtension hp hp1 n ψ := by
    let U : Set (realTypeSourceSubmodule p) := Subtype.val ⁻¹' V
    have hU : IsOpen U := hV.preimage continuous_subtype_val
    have hc : ContinuousOn (fun χ : realTypeSourceSubmodule p =>
        C.normalizedAction n 1 χ.val - sourceNormalizedActionComplexExtension hp hp1 n χ.val) U :=
      (hF.continuousOn.sub hG.continuousOn).comp continuous_subtype_val.continuousOn (fun _ hχ => hχ)
    apply sub_eq_zero.mp
    exact eq_of_continuousOn_of_sourceFiniteOpenGaps hp hp1 {n} hU hc 0
      (fun χ hχ hopen => by
        have hgap := hopen n (by simp)
        change canonicalPeriodicGap hp hp1 (periodOnePotential χ.val) (periodOnePotential_mem χ.val) n ≠ 0 at hgap
        have he := C.action_one_eq_sourceComplexAction_real χ (hAC hχ.1) n hn
        rw [C.action_eq_squaredGap_mul_normalizedAction n 1 hn χ.val (hAC hχ.1),hfactor χ.val hχ.2,
          sourcePeriodicGapDisplacement_apply] at he
        exact sub_eq_zero.mpr (mul_left_cancel₀ (pow_ne_zero 2 hgap) he)) ⟨ψ,hψr⟩ hψ
  obtain ⟨U,hU,hφU,hUV,heq⟩ := exists_local_eqOn_of_eqOn_realType hp φ.val φ.property.1
    V V hV hV ⟨hφA,hφB⟩ ⟨hφA,hφB⟩ _ _ hF.differentiableOn hG.differentiableOn
    (fun ψ hψ hψr => hreal ψ hψ.1 hψr)
  refine ⟨U,hU,hφU,fun ψ hψ => hAC (hUV hψ).1.1,?_,heq⟩
  intro k
  exact (hAn k).mono (fun ψ hψ => (hUV hψ).1.1)

/-- The collapsed inverse-frequency factor retains the true spectral midpoint. -/
theorem normalizedAction_zero_eq_midpoint_inv_mul_one_of_zeroGap
    (C : SourceDiagonalLaurentLocalChart hp hp1 φ) (n : ℤ) (hn : n ≠ 0)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball φ.val C.radius)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0) :
    C.normalizedAction n 0 ψ =
      (sourceStandardRootMidpoint hp hp1 ψ n)⁻¹ * C.normalizedAction n 1 ψ :=
  C.cauchy.laurentSquaredGapCircle_zero_eq_midpoint_inv_mul_one_of_zeroGap n ψ (C.source_subset hψ) _
    (C.contourRadius_bounds n).1 (C.contourRadius_bounds n).2 (C.zero_not_mem_contour_disc n hn) hgap

end SourceDiagonalLaurentLocalChart
end NLS.ZakharovShabat
