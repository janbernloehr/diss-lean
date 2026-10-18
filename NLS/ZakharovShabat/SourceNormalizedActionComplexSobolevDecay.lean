import NLS.ZakharovShabat.SourceCriticalFactorSobolevDecay
import NLS.ZakharovShabat.SourceNormalizedActionUniformCircleCorrection
import NLS.ZakharovShabat.SourceNormalizedActionUniformCircleComplexAgreement
import NLS.ZakharovShabat.SourceNormalizedActionComplexSequenceSpace
import NLS.ZakharovShabat.SourceNormalizedActionRootSequenceSpace

/-! # Complex Sobolev normalized-action and root decay

Exact common-circle agreement transfers the factor estimate to the actual normalized action. A finite-head bound and the principal-square-root inequality give inverse-bracket decay at every index.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The actual normalized action has inverse-bracket decay on a complex first-order Sobolev neighborhood. -/
theorem exists_local_normalizedSobolevActionDeviation_decay (φ : realTypeSourceLocus 2) :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ φ.val ∈ U ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ ψ ∈ U, ∀ n : ℤ,
        (1+|(n:ℝ)|)*‖sourceNormalizedActionDeviation (by simp) (by norm_num)
          (normalizedWeightedSource (SpectralWeight.sobolev 1 (by norm_num)) ψ) n‖ ≤ K := by
  let w := SpectralWeight.sobolev 1 (by norm_num)
  let L := normalizedWeightedSourceCLM (p := 2) w
  let φu : realTypeSourceSubmodule 2 :=
    ⟨L φ.val,normalizedWeightedSource_realType w φ.val φ.property⟩
  obtain ⟨Vf,hVf,hφf,Nf,F,hF,hfactor⟩ := exists_local_normalizedSobolevCriticalFactor_decay φ
  obtain ⟨Vg,hVg,hφg,M,hM,hgap⟩ := exists_local_normalizedSobolevCriticalOffset_majorants φ
  obtain ⟨Vc,hVc,hφc,Nc,C,hC,hcorr⟩ :=
    exists_local_sourceNormalizedAction_uniform_circle_correction (q := 2)
      (by simp) (by norm_num) (by norm_num) (by norm_num) (by norm_num) φu.val φu.property
  obtain ⟨Na,r,hr,hagree⟩ := exists_local_sourceNormalizedAction_uniform_circle_complex_agreement
    (by simp) (by norm_num) φu.val φu.property
  obtain ⟨Nt,Vt,hVt,hφt,htail⟩ := exists_local_sourceNormalizedAction_uniform_tail_circles
    (by simp) (by norm_num) φu.val
  obtain ⟨Vb,hVb,hφb,B,hbound⟩ := exists_local_sourceNormalizedActionDeviation_coeff_uniformNorm
    (q := 2) (by simp) (by norm_num) (by norm_num) (by norm_num) (by norm_num) φu.val φu.property
  let U := Vf ∩ (Vg ∩ L ⁻¹' (Vc ∩ (ball φu.val r ∩ (Vt ∩ Vb))))
  have hU : IsOpen U := hVf.inter (hVg.inter
    ((hVc.inter (isOpen_ball.inter (hVt.inter hVb))).preimage L.continuous))
  let N := max Nf (max Nc (max Na Nt))
  let K := 4*C*M^2+F+(1+(N:ℝ))*max 0 B
  refine ⟨U,hU,⟨hφf,hφg,hφc,mem_ball_self hr,hφt,hφb⟩,K,by dsimp only [K]; positivity,?_⟩
  intro ψ hψ n
  let χ := L ψ
  by_cases hn : N ≤ n.natAbs
  · have hNf : Nf ≤ n.natAbs := (le_max_left _ _).trans hn
    have hNc : Nc ≤ n.natAbs := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hn
    have hNa : Na ≤ n.natAbs :=
      (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)).trans hn
    have hNt : Nt ≤ n.natAbs :=
      (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)).trans hn
    obtain ⟨hseg,hdisc,_,_⟩ := htail χ hψ.2.2.2.2.1 n hNt
    have hτball := hseg (sourcePeriodicMidpoint_mem_segment (by simp) (by norm_num) χ n)
    have hτdisc := hdisc (mem_closedBall.mpr (mem_ball.mp hτball).le)
    have hf := hfactor ψ hψ.1 n hNf _ hτdisc
    have hc := hcorr χ hψ.2.2.1 n hNc
    rw [(hagree χ hψ.2.2.2.1 n hNa).1] at hc
    obtain ⟨G,_,hG,_,hGn,_,_⟩ := hgap ψ hψ.2.1
    let b := 1+|(n:ℝ)|
    let g := ‖sourcePeriodicGapDisplacement (by simp) (by norm_num) χ n‖
    have hb : 1 ≤ b := by dsimp only [b]; linarith [abs_nonneg (n:ℝ)]
    have hg : 0 ≤ g := norm_nonneg _
    have hbg : b*g ≤ M :=
      (hG n).trans ((lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞) ≠ 0) G n).trans hGn)
    have hg2 : b*g^2 ≤ M^2 := by
      have hsq := pow_le_pow_left₀ (mul_nonneg (by linarith : 0 ≤ b) hg) hbg 2
      nlinarith [sq_nonneg g]
    let ρ := sourceNormalizedActionComplexExtension (by simp) (by norm_num) n χ
    let E := I*sourceCriticalRootRatioExtension (by simp) (by norm_num) n χ
      (sourceStandardRootMidpoint (by simp) (by norm_num) χ n)
    have he : 4*ρ-1 = 4*(ρ-E/4)+(E-1) := by ring
    have hnorm : ‖4*ρ-1‖ ≤ 4*‖ρ-E/4‖+‖E-1‖ := by
      rw [he]
      exact (norm_add_le _ _).trans_eq (by rw [norm_mul]; norm_num)
    have hc' : ‖ρ-E/4‖ ≤ C*g^2 := by simpa only [norm_pow] using hc
    have hf' : b*‖E-1‖ ≤ F := hf
    have hmain : b*‖4*ρ-1‖ ≤ 4*C*M^2+F := by
      calc
        _ ≤ b*(4*‖ρ-E/4‖+‖E-1‖) := mul_le_mul_of_nonneg_left hnorm (by linarith)
        _ ≤ b*(4*(C*g^2)+‖E-1‖) := by gcongr
        _ = (4*C)*(b*g^2)+b*‖E-1‖ := by ring
        _ ≤ (4*C)*M^2+F := add_le_add (mul_le_mul_of_nonneg_left hg2 (by positivity)) hf'
        _ = _ := by ring
    exact hmain.trans (le_add_of_nonneg_right (by positivity))
  · obtain ⟨A,hA,hAn⟩ := hbound χ hψ.2.2.2.2.2
    have hsmall : |(n:ℝ)| ≤ (N:ℝ) := by
      have ha : n.natAbs ≤ N := by omega
      have hc : (n.natAbs:ℝ) ≤ (N:ℝ) := by exact_mod_cast ha
      simpa only [Nat.cast_natAbs,Int.cast_abs] using hc
    have hpoint : ‖sourceNormalizedActionDeviation (by simp) (by norm_num) χ n‖ ≤ max 0 B := by
      rw [← hA n]
      exact ((lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞) ≠ 0) A n).trans hAn).trans (le_max_right _ _)
    exact (mul_le_mul (by linarith : 1+|(n:ℝ)| ≤ 1+(N:ℝ)) hpoint (norm_nonneg _) (by positivity)).trans
      (le_add_of_nonneg_left (by positivity : 0 ≤ 4*C*M^2+F))

/-- The actual principal normalization root inherits inverse-bracket decay on the same complex neighborhood. -/
theorem exists_local_normalizedSobolevRootDeviation_decay (φ : realTypeSourceLocus 2) :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ φ.val ∈ U ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ ψ ∈ U, ∀ n : ℤ,
        (1+|(n:ℝ)|)*‖sourceNormalizedActionRootDeviation (by simp) (by norm_num)
          (normalizedWeightedSource (SpectralWeight.sobolev 1 (by norm_num)) ψ) n‖ ≤ K := by
  obtain ⟨U,hU,hφ,K,hK,hbound⟩ := exists_local_normalizedSobolevActionDeviation_decay φ
  refine ⟨U,hU,hφ,K,hK,?_⟩
  intro ψ hψ n
  have hs := norm_sqrt_sub_one_le (4*sourceNormalizedActionComplexExtension (by simp) (by norm_num) n
    (normalizedWeightedSource (SpectralWeight.sobolev 1 (by norm_num)) ψ))
  exact (mul_le_mul_of_nonneg_left hs (by positivity)).trans (hbound ψ hψ n)

end NLS.ZakharovShabat
