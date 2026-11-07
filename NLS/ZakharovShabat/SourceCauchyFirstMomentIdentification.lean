import NLS.ZakharovShabat.SourceHigherActionOneCommonAnalytic
import NLS.ZakharovShabat.SourceNormalizedWeightedActionCalibration
import NLS.ZakharovShabat.SourceHolomorphicRealCenteredBalls

/-! The SAME Cauchy first action moment equals the filled original
indexed higher action, including collapsed gaps. One complex source
ball gives this identity before ALL sufficiently high labels. -/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
variable {p : ℝ≥0∞} [Fact (1≤p)] {hp : p≠⊤} {hp1 : 1<p} {W : Set (CoeffPair p)}

theorem normalizedWeightedAction_one_eq_filled_of_real
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val∈ball C.discs.source.val C.discs.sourceRadius) (n : ℤ) :
    C.normalizedWeightedAction n 1 φ.val=sourceHigherActionOneNormalized hp hp1 n φ.val := by
  by_cases hg : sourcePeriodicGapDisplacement hp hp1 φ.val n=0
  · have hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem _) n=0 := by
      simpa only [sourcePeriodicGapDisplacement_apply] using hg
    rw [C.normalizedWeightedAction_collapsed n 1 φ.val hgap,pow_one,
      C.normalizedWeightedAction_zero_eq_canonical φ hφ n,
      sourceHigherActionOneNormalized_eq_midpoint_mul_of_gap_zero hp hp1 n φ.val hg]
  · obtain ⟨r,hr,_,hf⟩ := C.exists_ball_normalizedWeightedActions (sourceHigherActionAtlas hp hp1) φ hφ
    have h := (hf n 1).2 φ.val (mem_ball_self hr)
    have he : (sourceHigherActionAtlas hp hp1).action n 1 φ.val=sourceIndexedHigherAction hp hp1 n 1 φ.val :=
      ((sourceHigherActionAtlas hp hp1).action_eq_real φ n 1).trans (sourceIndexedHigherAction_eq_real hp hp1 φ n 1).symm
    rw [he] at h
    rw [sourceHigherActionOneNormalized_eq_quotient_of_gap_ne_zero hp hp1 n φ.val hg,h]
    simpa only [sourcePeriodicGapDisplacement_apply] using
      (mul_div_cancel_left₀ (C.normalizedWeightedAction n 1 φ.val) (pow_ne_zero 2 hg)).symm

theorem exists_local_normalizedWeightedAction_one_eq_filled
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val∈ball C.discs.source.val C.discs.sourceRadius) :
    ∃ N : ℕ, ∃ U : Set (CoeffPair p), IsOpen U ∧ φ.val∈U ∧
      U⊆ball C.discs.source.val C.discs.sourceRadius ∧ ∀ n : ℤ, N≤n.natAbs →
        AnalyticOnNhd ℂ (C.normalizedWeightedAction n 1) U ∧
        EqOn (C.normalizedWeightedAction n 1) (sourceHigherActionOneNormalized hp hp1 n) U := by
  obtain ⟨r,hr,hsub,hC⟩ := C.exists_ball_normalizedWeightedActions (sourceHigherActionAtlas hp hp1) φ hφ
  obtain ⟨N,V,hV,hφV,hA⟩ := exists_local_sourceHigherActionOneNormalized_common_analytic hp hp1 φ.val φ.property
  obtain ⟨s,hs,hball⟩ := Metric.mem_nhds_iff.mp ((hV.inter isOpen_ball).mem_nhds ⟨hφV,mem_ball_self hr⟩)
  have hsC : ball φ.val s⊆ball C.discs.source.val C.discs.sourceRadius := fun z hz => (hsub (hball hz).2).2
  refine ⟨N,ball φ.val s,isOpen_ball,mem_ball_self hs,hsC,?_⟩
  intro n hn
  have hc := (hC n 1).1.mono (fun _ hz => (hball hz).2)
  have ha := (hA n hn).mono (fun _ hz => (hball hz).1)
  refine ⟨hc,?_⟩
  have he := eqOn_sourceRealCenteredBalls_of_real_agreement hp ⟨φ.val,φ.property⟩ ⟨φ.val,φ.property⟩ s s
    (C.normalizedWeightedAction n 1) (sourceHigherActionOneNormalized hp hp1 n) hc.differentiableOn ha.differentiableOn
    (fun χ hχ => C.normalizedWeightedAction_one_eq_filled_of_real ⟨χ.val,χ.property⟩ (hsC hχ.1) n)
  exact fun z hz => he ⟨hz,hz⟩

end NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
