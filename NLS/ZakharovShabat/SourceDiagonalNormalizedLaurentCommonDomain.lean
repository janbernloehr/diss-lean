import NLS.ZakharovShabat.SourceDiagonalNormalizedLaurentAction

/-! # One complex domain for all normalized inverse-frequency actions

A single real-centered ball supports the rationalized contour factors at
all noncentral indices. Real open-gap density identifies each ordinary
factor, and holomorphic continuation identifies it on the entire ball.
No infinite intersection of index-dependent neighborhoods is used.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceDiagonalLaurentLocalChart
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {φ : realDiagonalSourceLocus p}

/-- Every noncentral normalized factor is analytic on one real-centered
ball; the level-one factors all agree with the ordinary action factors. -/
theorem exists_all_normalizedAction_analytic
    (C : SourceDiagonalLaurentLocalChart hp hp1 φ) :
    ∃ r : ℝ, 0 < r ∧ ball φ.val r ⊆ ball φ.val C.radius ∧
      (∀ n : ℤ, n ≠ 0 → ∀ k : ℤ, AnalyticOnNhd ℂ (C.normalizedAction n k) (ball φ.val r)) ∧
      ∀ n : ℤ, n ≠ 0 → EqOn (C.normalizedAction n 1)
        (sourceNormalizedActionComplexExtension hp hp1 n) (ball φ.val r) := by
  obtain ⟨G,hG,_,hrealG,hdata⟩ := exists_global_source_analytic_midpoint_squaredGap hp hp1
  obtain ⟨B,hB,hφB,hBn,hfactor⟩ :=
    exists_local_sourceNormalizedAction_allIndices_analytic_factor hp hp1 φ.val φ.property.1
  obtain ⟨r,hr,hsub⟩ := Metric.isOpen_iff.mp ((isOpen_ball.inter hG).inter hB) φ.val
    ⟨⟨mem_ball_self C.radius_pos,hrealG φ.property.1⟩,hφB⟩
  have hC : ball φ.val r ⊆ ball φ.val C.radius := fun ψ hψ => (hsub hψ).1.1
  have hroot : IsOpen (sourceCanonicalRootJointDomain hp hp1 (ball φ.val r)) := by
    have he : sourceCanonicalRootJointDomain hp hp1 (ball φ.val r) =
        sourceCanonicalRootJointDomain hp hp1 (ball φ.val C.radius) ∩ Prod.snd ⁻¹' ball φ.val r := by
      ext t
      exact ⟨fun ht => ⟨⟨hC ht.1,ht.2⟩,ht.1⟩,fun ht => ⟨ht.2,ht.1.2⟩⟩
    rw [he]
    exact C.root_domain_open.inter (isOpen_ball.preimage continuous_snd)
  have hAn (n : ℤ) (hn : n ≠ 0) (k : ℤ) :
      AnalyticOnNhd ℂ (C.normalizedAction n k) (ball φ.val r) :=
    C.cauchy.laurentSquaredGapCircle_analytic n k _
      (C.contourRadius_bounds n).1 (C.contourRadius_bounds n).2 (C.zero_not_mem_contour_disc n hn)
      _ isOpen_ball (fun ψ hψ => C.source_subset (hC hψ)) hroot
      (fun ψ hψ => (hdata ψ (hsub hψ).1.2 n).1)
      (fun ψ hψ => (hdata ψ (hsub hψ).1.2 n).2)
  refine ⟨r,hr,hC,hAn,?_⟩
  intro n hn ψ hψ
  have hF := hAn n hn 1
  have hG : AnalyticOnNhd ℂ (sourceNormalizedActionComplexExtension hp hp1 n) (ball φ.val r) :=
    (hBn n).mono (fun χ hχ => (hsub hχ).2)
  have hreal (χ : realTypeSourceLocus p) (hχ : χ.val ∈ ball φ.val r) :
      C.normalizedAction n 1 χ.val = sourceNormalizedActionComplexExtension hp hp1 n χ.val := by
    let U : Set (realTypeSourceSubmodule p) := Subtype.val ⁻¹' ball φ.val r
    have hc : ContinuousOn (fun θ : realTypeSourceSubmodule p =>
        C.normalizedAction n 1 θ.val-sourceNormalizedActionComplexExtension hp hp1 n θ.val) U :=
      (hF.continuousOn.sub hG.continuousOn).comp continuous_subtype_val.continuousOn (fun _ hθ => hθ)
    apply sub_eq_zero.mp
    exact eq_of_continuousOn_of_sourceFiniteOpenGaps hp hp1 {n}
      (isOpen_ball.preimage continuous_subtype_val) hc 0
      (fun θ hθ hopen => by
        have hgap := hopen n (by simp)
        change canonicalPeriodicGap hp hp1 (periodOnePotential θ.val) (periodOnePotential_mem θ.val) n ≠ 0 at hgap
        have he := C.action_one_eq_sourceComplexAction_real θ (hC hθ) n hn
        rw [C.action_eq_squaredGap_mul_normalizedAction n 1 hn θ.val (hC hθ),
          hfactor θ.val (hsub hθ).2 n,sourcePeriodicGapDisplacement_apply] at he
        exact sub_eq_zero.mpr (mul_left_cancel₀ (pow_ne_zero 2 hgap) he)) χ hχ
  exact eqOn_sourceRealCenteredBalls_of_real_agreement hp ⟨φ.val,φ.property.1⟩ ⟨φ.val,φ.property.1⟩ r r
    _ _ hF.differentiableOn hG.differentiableOn (fun χ hχ => hreal χ hχ.1) ⟨hψ,hψ⟩

end SourceDiagonalLaurentLocalChart

/-- All normalized inverse-frequency actions are Banach analytic on one
complex ball around a real diagonal, with simultaneous exact factorization. -/
theorem exists_local_sourceNormalizedDiagonalLaurentAction_allIndices_analytic_factor
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realDiagonalSourceLocus p) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ.val ∈ U ∧
      (∀ n : ℤ, n ≠ 0 → AnalyticOnNhd ℂ (sourceNormalizedDiagonalLaurentAction hp hp1 n) U) ∧
      ∀ ψ ∈ U, ∀ n : ℤ, n ≠ 0 → sourceDiagonalLaurentAction hp hp1 n 0 ψ =
        (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem _) n)^2 *
          sourceNormalizedDiagonalLaurentAction hp hp1 n ψ := by
  let C := (sourceDiagonalLaurentAtlas hp hp1).localChart φ
  obtain ⟨r,hr,hC,hAn,hone⟩ := C.exists_all_normalizedAction_analytic
  have heq (n : ℤ) (hn : n ≠ 0) : EqOn (sourceNormalizedDiagonalLaurentAction hp hp1 n)
      (C.normalizedAction n 0) (ball φ.val r) := by
    intro ψ hψ
    have hlocal : sourceDiagonalLaurentAction hp hp1 n 0 ψ = C.action n 0 ψ :=
      (sourceDiagonalLaurentAtlas hp hp1).action_eq_local n 0 hn φ (hC hψ)
    by_cases hg : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem _) n = 0
    · rw [sourceNormalizedDiagonalLaurentAction,if_pos hg,← hone n hn hψ]
      exact (C.normalizedAction_zero_eq_midpoint_inv_mul_one_of_zeroGap n hn ψ (hC hψ) hg).symm
    · rw [sourceNormalizedDiagonalLaurentAction,if_neg hg,hlocal,
        C.action_eq_squaredGap_mul_normalizedAction n 0 hn ψ (hC hψ)]
      exact mul_div_cancel_left₀ _ (pow_ne_zero 2 hg)
  refine ⟨ball φ.val r,isOpen_ball,mem_ball_self hr,?_,?_⟩
  · intro n hn ψ hψ
    apply (hAn n hn 0 ψ hψ).congr
    filter_upwards [isOpen_ball.mem_nhds hψ] with χ hχ
    exact (heq n hn hχ).symm
  · intro ψ hψ n hn
    rw [heq n hn hψ]
    exact ((sourceDiagonalLaurentAtlas hp hp1).action_eq_local n 0 hn φ (hC hψ)).trans
      (C.action_eq_squaredGap_mul_normalizedAction n 0 hn ψ (hC hψ))

end NLS.ZakharovShabat
