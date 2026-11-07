import NLS.ZakharovShabat.SourceRetainedEtaRemainderAnalytic
import NLS.ZakharovShabat.SourceWeightedMidpointBound
import NLS.ZakharovShabat.SourceWeightedGapSequence

/-! The SAME own-index eta remainder has inverse-index decay on one
complex normalized first-order source neighborhood. Actual midpoint and
gap bounds retain all low and collapsed labels and the original roots. -/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

theorem exists_local_normalizedWeighted_own_eta_decay
    (D : SourceBirkhoffMapComplexData (by norm_num) (by norm_num) W₀ B W s)
    (w : SpectralWeight) (hw : ∀ n : ℤ,1+|(n:ℝ)|≤w (2*n)) (φ : realTypeSourceLocus 2) :
    ∃ U : Set (CoeffPair 2),IsOpen U ∧ φ.val∈U ∧
      (∀ ψ∈U,normalizedWeightedSource w ψ∈W) ∧
      (∀ n : ℤ,AnalyticOnNhd ℂ (fun ψ => sourceAngularEtaRemainder (by norm_num) (by norm_num) n s
        (normalizedWeightedSource w ψ)) U) ∧
      ∃ K : ℝ,0≤K ∧ ∀ ψ∈U,∀ n : ℤ,(1+|(n:ℝ)|)*‖sourceAngularEtaRemainder (by norm_num) (by norm_num) n s
        (normalizedWeightedSource w ψ)‖≤K := by
  let φu : realTypeSourceSubmodule 2 := ⟨normalizedWeightedSource w φ.val,normalizedWeightedSource_realType w φ.val φ.property⟩
  obtain ⟨Va,hVa,hφa,hVaW,ha⟩ := D.exists_local_ownEtaRemainder_common_analytic φu
  obtain ⟨Vr,hVr,hφr,_hVrW,C,hC,hr⟩ := D.exists_local_uniform_etaRemainder_gap_bound φu
  obtain ⟨Vs,hVs,hφs,_hVsW,M,hM,hs⟩ := D.exists_local_normalizedWeightedMidpoint_bound w φ
  let L := normalizedWeightedSourceCLM (p := 2) w
  let S := (normalizedWeightedPeriodOne (p := 2) w).toContinuousLinearMap
  have hSL : ∀ b,weightedBaseToPair w (S b)=periodOnePotential (L b) :=
    fun b => weightedBaseToPair_normalizedWeightedPeriodOne w b
  obtain ⟨Vg,hVg,hφg,G,hG,hg⟩ := exists_local_sourceWeightedGapSequence_bound (by norm_num) (by norm_num) w L S hSL φ.val
  let U := (Vs∩Vg)∩L ⁻¹' (Vr∩Va)
  refine ⟨U,(hVs.inter hVg).inter ((hVr.inter hVa).preimage L.continuous),⟨⟨hφs,hφg⟩,hφr,hφa⟩,
    (fun ψ hψ => hVaW hψ.2.2),(fun n ψ hψ => (ha n (L ψ) hψ.2.2).comp (L.analyticAt ψ)),C*(M+G),by positivity,?_⟩
  intro ψ hψ n
  obtain ⟨A,hA,hAn⟩ := hs ψ hψ.1.1
  let g := sourceWeightedGapSequence (by norm_num) (by norm_num) w L S hSL ψ
  have hgc : g n=(w (2*n):ℂ)*sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ) n := rfl
  have hAc : (w (2*n))*‖sourceDirichletMidpointDisplacement (by norm_num) (by norm_num) (L ψ) n‖≤M := by
    have h := (lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞)≠0) A n).trans hAn
    rw [hA,norm_mul,Complex.norm_real,Real.norm_of_nonneg (w.positive _).le] at h
    exact h
  have hGc : (w (2*n))*‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ) n‖≤G := by
    have h := (lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞)≠0) g n).trans (hg ψ hψ.1.2)
    rw [hgc,norm_mul,Complex.norm_real,Real.norm_of_nonneg (w.positive _).le] at h
    exact h
  have hb := hr (L ψ) hψ.2.1 n
  rw [←sourceDirichletMidpointDisplacement_apply] at hb
  have hb' : ‖sourceAngularEtaRemainder (by norm_num) (by norm_num) n s (L ψ)‖≤
      C*(‖sourceDirichletMidpointDisplacement (by norm_num) (by norm_num) (L ψ) n‖+
        ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ) n‖) :=
    hb.trans (mul_le_mul_of_nonneg_left (by linarith [norm_nonneg (sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ) n)]) hC)
  calc
    _ ≤ (w (2*n))*‖sourceAngularEtaRemainder (by norm_num) (by norm_num) n s (L ψ)‖ :=
      mul_le_mul_of_nonneg_right (hw n) (norm_nonneg _)
    _ ≤ (w (2*n))*(C*(‖sourceDirichletMidpointDisplacement (by norm_num) (by norm_num) (L ψ) n‖+
        ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ) n‖)) :=
      mul_le_mul_of_nonneg_left hb' (w.positive _).le
    _ = C*((w (2*n))*‖sourceDirichletMidpointDisplacement (by norm_num) (by norm_num) (L ψ) n‖+
        (w (2*n))*‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ) n‖) := by ring
    _ ≤ C*(M+G) := mul_le_mul_of_nonneg_left (add_le_add hAc hGc) hC

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
