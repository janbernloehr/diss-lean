import NLS.ZakharovShabat.SourceNormalizedSecondMoment
import NLS.ZakharovShabat.SourceNormalizedActionRootAnalytic
import NLS.ZakharovShabat.SourceNormalizedActionFree
import NLS.ZakharovShabat.SourceSecondMomentFrequencyAnalytic

/-! # The leading action coefficient of the actual second moments -/
noncomputable section
open Set Metric Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceAbelianMomentAtlas
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W V : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Near zero each actual second moment is the selected action times a
continuous coefficient whose free value is pi times the Kronecker delta. -/
theorem exists_secondMoment_action_factor_at_zero
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiNormalizedComplexExtension hp hp1 V s)
    (hV : IsOpen V) (hrealV : realTypeSourceLocus p ⊆ V) (n k : ℤ) :
    ∃ f : CoeffPair p → ℂ, ContinuousAt f 0 ∧ f 0 = (if k = n then (Real.pi : ℂ) else 0) ∧
      ∀ᶠ ψ in 𝓝 (0 : CoeffPair p), A.moment n k 2 ψ = sourceComplexAction hp hp1 k ψ * f ψ := by
  have hreal : IsRealType (CoeffPair.toMax p (0 : CoeffPair p)) := (0 : realTypeSourceSubmodule p).property
  obtain ⟨D,_⟩ := A.exists_errorDomain hs hV hrealV
  obtain ⟨W',_,_,hfamily⟩ := exists_sourceFullAbelianUniformCauchyFamilies hp hp1
  obtain ⟨C,hCsource⟩ := hfamily (0 : realTypeSourceSubmodule p)
  have hC : (0 : CoeffPair p) ∈ ball C.discs.source.val C.discs.sourceRadius := by
    rw [hCsource]
    exact mem_ball_self C.discs.sourceRadius_pos
  obtain ⟨T,hT,hzero,hB,hfactor⟩ := exists_local_sourceNormalizedAction_analytic_factor hp hp1 0 hreal k
  let b := sourceNormalizedActionComplexExtension hp hp1 k
  have hb : ContinuousAt b 0 := (hB 0 hzero).continuousAt
  have hbzero : b 0 = 1/4 := sourceNormalizedActionComplexExtension_zero_source hp hp1 k
  have hbne : b 0 ≠ 0 := by rw [hbzero]; norm_num
  let f := fun ψ => C.normalizedSecondMoment s n k ψ / b ψ
  have hf : ContinuousAt f 0 :=
    (C.continuousAt_normalizedSecondMoment_zero hC hs.toSourcePsiIsolatingComplexExtension
      (hrealV hreal) n k).div hb hbne
  refine ⟨f,hf,?_,?_⟩
  · dsimp only [f]
    rw [C.normalizedSecondMoment_zero hC hs.toSourcePsiIsolatingComplexExtension.branch_zero,hbzero]
    split_ifs <;> ring
  · have hne : ∀ᶠ ψ in 𝓝 (0 : CoeffPair p), b ψ ≠ 0 := hb.eventually_ne hbne
    filter_upwards [hT.mem_nhds hzero,D.isOpen_domain.mem_nhds (D.real_subset hreal),
      isOpen_ball.mem_nhds hC,hne] with ψ hψT hψD hψC hψne
    rw [C.moment_two_eq_squaredGap_mul_normalized A D ψ hψD hψC n k,hfactor ψ hψT]
    dsimp only [f,b] at *
    field_simp

/-- On real sources with at most one open action, the frequency has a
continuous action coefficient with free value minus twice the Kronecker delta. -/
theorem exists_singleAction_frequency_factor_at_zero
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiNormalizedComplexExtension hp hp1 V s)
    (hV : IsOpen V) (hrealV : realTypeSourceLocus p ⊆ V) (n k : ℤ) :
    ∃ f : CoeffPair p → ℂ, ContinuousAt f 0 ∧ f 0 = (if k = n then (-2 : ℂ) else 0) ∧
      ∀ᶠ ψ in 𝓝 (0 : CoeffPair p), IsRealType (CoeffPair.toMax p ψ) →
        (∀ j : ℤ, j ≠ k → sourceComplexAction hp hp1 j ψ = 0) →
        A.renormalizedFrequency n ψ = sourceComplexAction hp hp1 k ψ * f ψ := by
  obtain ⟨g,hg,hgzero,hfactor⟩ := A.exists_secondMoment_action_factor_at_zero hs hV hrealV n k
  let c : ℂ := -(4/(2*Real.pi):ℂ)
  refine ⟨fun ψ => c*g ψ,continuousAt_const.mul hg,?_,?_⟩
  · change c*g (0 : CoeffPair p) = _
    rw [hgzero]
    dsimp only [c]
    split_ifs
    · have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      field_simp
      norm_num
    · ring
  · filter_upwards [hfactor] with ψ hψ hreal hsupport
    have hoff (j : ℤ) (hjk : j ≠ k) : A.moment n j 2 ψ = 0 := by
      have hI := hsupport j hjk
      rw [sourceComplexAction_eq_sourceRealAction hp hp1 j ψ hreal] at hI
      have hgap := (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero hp hp1 ψ hreal j).2.2.mp hI
      rw [sourcePeriodicGapDisplacement_apply] at hgap
      exact A.moment_succ_of_collapsed ψ (A.realType_subset_domain hreal) n j hgap 1
    unfold renormalizedFrequency
    rw [tsum_eq_single k hoff,hψ]
    dsimp only [c]
    ring

end NLS.ZakharovShabat.SourceAbelianMomentAtlas
