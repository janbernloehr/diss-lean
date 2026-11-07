import NLS.ZakharovShabat.SourceRawActionGapError
import NLS.ZakharovShabat.SourcePrimitiveSobolevUniformLittleO
import NLS.ZakharovShabat.SourceWeightedActionAffineRemainder
import NLS.ZakharovShabat.SourceUniformGapBoundaryBound
import NLS.ComplexAnalysis.WeightedAffineQuadraticUniformTail

/-! Uniform little-o of the actual first weighted action relative to
two literal gap factors, on a fixed complex Sobolev neighborhood. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
variable {W : Set (CoeffPair 2)}

theorem exists_local_sobolev_firstWeightedAction_uniform_littleO
    (C : SourceFullAbelianUniformCauchyFamily (by norm_num) (by norm_num) W)
    (A : SourceHigherActionAtlas (by norm_num) (by norm_num))
    (t : ℝ) (ht : 0<t) (ht1 : t<1)
    (φ : realTypeSourceSubmodule 2)
    (hφC : normalizedWeightedSourceCLM (p := 2) (sourceSobolevSpectralWeight t ht.le) φ.val∈
      ball C.discs.source.val C.discs.sourceRadius) :
    let L := normalizedWeightedSourceCLM (p := 2) (sourceSobolevSpectralWeight t ht.le)
    ∃ T : Set (CoeffPair 2), IsOpen T ∧ φ.val∈T ∧ T⊆L ⁻¹' A.domain ∧
      ∀ ε > (0:ℝ), ∃ K : ℕ, ∀ ψ∈T, ∀ n : ℤ, K≤n.natAbs →
        Weight.sobolev (t-1) n*‖A.action n 1 (L ψ)-
          ((Real.pi:ℂ)*n)*(sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ) n)^2/4‖≤
            ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ) n‖^2*ε := by
  intro L
  have hrφ := normalizedWeightedSource_realType (sourceSobolevSpectralWeight t ht.le) φ.val φ.property
  let φ₀ : realTypeSourceSubmodule 2 := ⟨L φ.val,hrφ⟩
  obtain ⟨Ts,hTs,hφs,hprimitive⟩ :=
    exists_local_sobolev_primitive_gap_uniform_littleO t ht ht1 φ
  obtain ⟨b,hb,hbsub,hNa⟩ := C.exists_ball_normalizedWeightedActions A φ₀ hφC
  obtain ⟨Tb,hTb,hφb,hbC,B,hB,hboundary⟩ := C.exists_local_uniform_gapBoundary_bound φ₀ hφC
  obtain ⟨_Ng,_hNg,Tg,hTg,hφg,H,hH,hgap⟩ := exists_uniform_small_sourcePeriodicGapDisplacement
    (by norm_num : (2 : ℝ≥0∞)≠⊤) (by norm_num) (L φ.val) (by norm_num : (0 : ℝ)<1)
  obtain ⟨_Nm,_hNm,Tm,hTm,hφm,J,hJ,hmid⟩ := exists_uniform_small_sourcePeriodicMidpointDisplacement
    (by norm_num : (2 : ℝ≥0∞)≠⊤) (by norm_num) (L φ.val) (by norm_num : (0 : ℝ)<1)
  let T := Ts∩L ⁻¹' ((ball φ₀.val b∩Tb)∩(Tg∩Tm))
  have hT : IsOpen T := hTs.inter
    (((isOpen_ball.inter hTb).inter (hTg.inter hTm)).preimage L.continuous)
  have hφball : L φ.val∈ball φ₀.val b := mem_ball_self hb
  have hφT : φ.val∈T := ⟨hφs,⟨hφball,hφb⟩,hφg,hφm⟩
  refine ⟨T,hT,hφT,(fun ψ hψ => (hbsub hψ.2.1.1).1),?_⟩
  intro ε hε
  let P := H*B/2+J/4
  let Q := Real.pi+J
  have hP : 0≤P := by dsimp only [P];positivity
  have hQ : 0≤Q := by dsimp only [Q];positivity
  let η := ε/(P+Q+1)
  have hden : 0<P+Q+1 := by linarith
  have hη : 0<η := div_pos hε hden
  have hηsum : η*(P+Q)≤ε := by
    have he : η*(P+Q+1)=ε := div_mul_cancel₀ ε hden.ne'
    nlinarith
  obtain ⟨Kp,hKp⟩ := hprimitive η hη
  obtain ⟨Kr,hKr⟩ := Weight.exists_sobolev_ratio_tail t 1 ht1 hη
  refine ⟨max Kp Kr,?_⟩
  intro ψ hψ n hn
  have hnp : Kp≤n.natAbs := (le_max_left _ _).trans hn
  have hnr : Kr≤n.natAbs := (le_max_right _ _).trans hn
  have hψC := hbC hψ.2.1.2
  let γ := canonicalPeriodicGap (by norm_num) (by norm_num) (periodOnePotential (L ψ)) (periodOnePotential_mem _) n
  let τ := sourceStandardRootMidpoint (by norm_num) (by norm_num) (L ψ) n
  let w := Weight.sobolev t n
  let v := Weight.sobolev 1 n
  have hw : 0<w := (Weight.sobolev t).positive n
  have hv : 1≤v := by
    simpa only [Weight.sobolev_zero_apply] using Weight.sobolev_mono (by norm_num : (0 : ℝ)≤1) n
  have hγ : ‖γ‖≤H := by
    have h := (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞)≠0)
      (sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ)) n).trans (hgap (L ψ) hψ.2.2.1).1
    simpa only [sourcePeriodicGapDisplacement_apply] using h
  have hμ : ‖τ-(Real.pi:ℂ)*n‖≤J := by
    have h := (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞)≠0)
      (sourcePeriodicMidpointDisplacement (by norm_num) (by norm_num) (L ψ)) n).trans (hmid (L ψ) hψ.2.2.2).1
    simpa only [sourcePeriodicMidpointDisplacement_apply,sourceStandardRootMidpoint] using h
  have hτ : ‖τ‖≤v*(Real.pi+J) := by
    have h := norm_add_le (τ-(Real.pi:ℂ)*n) ((Real.pi:ℂ)*n)
    rw [sub_add_cancel,norm_mul,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le,Complex.norm_intCast] at h
    have hv' : v=1+|(n:ℝ)| := by simp only [v,Weight.sobolev_apply,Real.rpow_one]
    rw [hv']
    nlinarith [Real.pi_pos,mul_nonneg (abs_nonneg (n:ℝ)) hJ]
  have he : ∀ θ∈Icc (0 : ℝ) Real.pi,
      ‖C.gapBoundary n (L ψ) θ true-I*sourceStandardRootGapBoundary (by norm_num) (by norm_num) (L ψ) n θ true‖≤
        ‖γ‖*(η/w) := by
    intro θ hθ
    rw [← mul_div_assoc]
    have hp := hKp ψ hψ.1 W C hψC n hnp θ hθ true
    apply (le_div_iff₀ hw).mpr
    rw [mul_comm]
    simpa only [sourcePeriodicGapDisplacement_apply] using hp
  have hz := C.norm_raw_normalizedWeightedAction_zero_error_le (L ψ) hψC n (η/w) he
  have hz' : w*‖γ^2*C.normalizedWeightedAction n 0 (L ψ)-γ^2/4‖≤‖γ‖^2*η := by
    have hd : ‖γ^2*C.normalizedWeightedAction n 0 (L ψ)-γ^2/4‖≤(‖γ‖^2*η)/w := by
      simpa only [mul_div_assoc] using hz
    rw [mul_comm w]
    exact (le_div_iff₀ hw).mp hd
  have h₁ : ‖C.normalizedWeightedAction n 1 (L ψ)-τ*C.normalizedWeightedAction n 0 (L ψ)‖≤‖γ‖*B/2 := by
    apply C.norm_normalizedWeightedAction_one_affine_remainder_le (L ψ) hψC n (‖γ‖*B)
    intro θ hθ
    simpa only [sourcePeriodicGapDisplacement_apply] using hboundary (L ψ) hψ.2.1.2 n θ hθ
  have hweighted := NLS.ComplexAnalysis.weighted_affine_quadratic_remainder_tail_bound w v H B η
    (Real.pi+J) J hw (zero_lt_one.trans_le hv) hB (by positivity)
    γ (C.normalizedWeightedAction n 0 (L ψ)) (C.normalizedWeightedAction n 1 (L ψ)) τ
    ((Real.pi:ℂ)*n) hγ hτ hμ h₁ hz'
  have hwv : Weight.sobolev (t-1) n=w/v := by
    apply (eq_div_iff ((Weight.sobolev 1).positive n).ne').mpr
    dsimp only [w,v]
    rw [← Weight.sobolev_add,sub_add_cancel]
  rw [(hNa n 1).2 (L ψ) hψ.2.1.1,hwv]
  have hratio : w/v≤η := (hKr n hnr).le
  have hsmall : (w/v)*P+Q*η≤ε := by
    calc
      _ ≤ η*P+Q*η := by gcongr
      _ = η*(P+Q) := by ring
      _ ≤ ε := hηsum
  have hout := hweighted.trans (mul_le_mul_of_nonneg_left hsmall (sq_nonneg ‖γ‖))
  simpa only [sourcePeriodicGapDisplacement_apply] using hout

end NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
