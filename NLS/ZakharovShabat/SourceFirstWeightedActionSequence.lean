import NLS.ZakharovShabat.SourceCauchyNormalizedActionSequence
import NLS.ZakharovShabat.SourceWeightedActionAffineRemainder
import NLS.ZakharovShabat.SourceUniformGapBoundaryBound
import NLS.ZakharovShabat.SourcePeriodicMidpointAsymptotics
import NLS.ZakharovShabat.SourcePeriodicGapTails

/-! After division by the original signed frequency index, the first
weighted normalized action differs from pi/4 by a bounded analytic
Hilbert packet. No selected gap is divided out. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
variable {W : Set (CoeffPair 2)}

theorem exists_ball_firstWeightedAction_error_l2
    (C : SourceFullAbelianUniformCauchyFamily (by norm_num) (by norm_num) W)
    (φ : realTypeSourceSubmodule 2) (hφC : φ.val∈ball C.discs.source.val C.discs.sourceRadius) :
    ∃ r : ℝ, 0<r ∧ ball φ.val r⊆ball C.discs.source.val C.discs.sourceRadius ∧
      ∃ M : ℝ, 0≤M ∧ ∃ G : CoeffPair 2 → Coeff 2,
        AnalyticOnNhd ℂ G (ball φ.val r) ∧
        (∀ ψ∈ball φ.val r, ∀ n : ℤ, G ψ n=
          if n=0 then 0 else 4*C.normalizedWeightedAction n 1 ψ/(n : ℂ)-(Real.pi : ℂ)) ∧
        ∀ ψ∈ball φ.val r, ‖G ψ‖≤M := by
  obtain ⟨T,hT,hφT,hTC,B,hB,hboundary⟩ := C.exists_local_uniform_gapBoundary_bound φ hφC
  obtain ⟨a,ha,_haC,_hagree,M0,hM0,G0,_hG0,hval0,hnorm0⟩ := C.exists_ball_normalizedWeightedAction_zero_l2 φ hφC
  obtain ⟨b,hb,_hbC,hNb⟩ := C.exists_ball_normalizedWeightedActions
    (sourceHigherActionAtlas (by norm_num) (by norm_num)) φ hφC
  obtain ⟨_Ng,_hNg,Tg,hTg,hφg,H,hH,hgap⟩ := exists_uniform_small_sourcePeriodicGapDisplacement
    (by norm_num : (2 : ℝ≥0∞)≠⊤) (by norm_num) φ.val (by norm_num : (0 : ℝ)<1)
  obtain ⟨_Nm,_hNm,Tm,hTm,hφm,J,hJ,hmid⟩ := exists_uniform_small_sourcePeriodicMidpointDisplacement
    (by norm_num : (2 : ℝ≥0∞)≠⊤) (by norm_num) φ.val (by norm_num : (0 : ℝ)<1)
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp
    (((hT.inter isOpen_ball).inter (isOpen_ball.inter (hTg.inter hTm))).mem_nhds
      ⟨⟨hφT,mem_ball_self ha⟩,mem_ball_self hb,hφg,hφm⟩)
  let U := ball φ.val r
  let M := 2*B*H+(M0+1)*J+Real.pi*M0
  have hM : 0≤M := by dsimp only [M]; positivity
  let f := fun ψ n => if n=0 then (0 : ℂ) else 4*C.normalizedWeightedAction n 1 ψ/(n : ℂ)-(Real.pi : ℂ)
  have hUC (ψ : CoeffPair 2) (hψ : ψ∈U) := hTC (hsub hψ).1.1
  have hf (n : ℤ) : AnalyticOnNhd ℂ (fun ψ => f ψ n) U := by
    by_cases hn : n=0
    · simpa only [f,if_pos hn] using (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : CoeffPair 2 => (0 : ℂ)) U)
    · intro ψ hψ
      change AnalyticAt ℂ (fun ψ => if n=0 then (0 : ℂ) else 4*C.normalizedWeightedAction n 1 ψ/(n : ℂ)-(Real.pi : ℂ)) ψ
      simp only [if_neg hn]
      exact ((analyticAt_const.mul ((hNb n 1).1 ψ (hsub hψ).2.1)).div_const).sub analyticAt_const
  have hbounded (ψ : CoeffPair 2) (hψ : ψ∈U) : ∃ v : Coeff 2, (∀ n, v n=f ψ n) ∧ ‖v‖≤M := by
    let γ := sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ
    let μ := sourcePeriodicMidpointDisplacement (by norm_num) (by norm_num) ψ
    let Z : Coeff 2 := ((2*B : ℝ) : ℂ) • Coeff.magnitude γ+
      ((M0+1 : ℝ) : ℂ) • Coeff.magnitude μ+(Real.pi : ℂ) • Coeff.magnitude (G0 ψ)
    have hZn (n : ℤ) : ‖Z n‖=2*B*‖γ n‖+(M0+1)*‖μ n‖+Real.pi*‖G0 ψ n‖ := by
      simp only [Z,lp.coeFn_add,Pi.add_apply,lp.coeFn_smul,Pi.smul_apply,Coeff.magnitude_apply,
        smul_eq_mul,← Complex.ofReal_mul,← Complex.ofReal_add,Complex.norm_real,
        Real.norm_of_nonneg (by positivity : 0≤2*B*‖γ n‖+(M0+1)*‖μ n‖+Real.pi*‖G0 ψ n‖)]
    have hpoint (n : ℤ) : ‖f ψ n‖≤‖Z n‖ := by
      by_cases hn : n=0
      · simp only [f,if_pos hn,norm_zero]
        exact norm_nonneg _
      have hnC : (n : ℂ)≠0 := by exact_mod_cast hn
      have hn1 : 1≤‖(n : ℂ)‖ := by
        rw [Complex.norm_intCast]
        exact_mod_cast Int.one_le_abs hn
      let τ := sourceStandardRootMidpoint (by norm_num) (by norm_num) ψ n
      let A0 := C.normalizedWeightedAction n 0 ψ
      let A1 := C.normalizedWeightedAction n 1 ψ
      have hR : ‖A1-τ*A0‖≤‖γ n‖*B/2 :=
        C.norm_normalizedWeightedAction_one_affine_remainder_le ψ (hUC ψ hψ) n (‖γ n‖*B)
          (fun θ hθ => hboundary ψ (hsub hψ).1.1 n θ hθ)
      have hA0 : ‖4*A0‖≤M0+1 := by
        have h := norm_add_le (G0 ψ n) (1 : ℂ)
        rw [hval0 ψ (hsub hψ).1.2 n,sub_add_cancel,norm_one] at h
        have hn0 := (lp.norm_apply_le_norm (by norm_num) (G0 ψ) n).trans (hnorm0 ψ (hsub hψ).1.2)
        rw [hval0 ψ (hsub hψ).1.2 n] at hn0
        linarith
      have hμ : μ n=τ-(Real.pi : ℂ)*n := by
        exact sourcePeriodicMidpointDisplacement_apply (by norm_num) (by norm_num) ψ n
      have he : 4*A1/(n : ℂ)-(Real.pi : ℂ)=
          (4*(A1-τ*A0)+μ n*(4*A0))/(n : ℂ)+(Real.pi : ℂ)*(4*A0-1) := by
        rw [hμ]
        field_simp
        ring
      have he0 : 4*A0-1=G0 ψ n := (hval0 ψ (hsub hψ).1.2 n).symm
      rw [show f ψ n=4*A1/(n : ℂ)-(Real.pi : ℂ) from if_neg hn,he]
      have hnum : ‖4*(A1-τ*A0)+μ n*(4*A0)‖≤4*‖A1-τ*A0‖+‖μ n‖*‖4*A0‖ := by
        simpa only [norm_mul,norm_ofNat] using norm_add_le (4*(A1-τ*A0)) (μ n*(4*A0))
      have hsplit := norm_add_le ((4*(A1-τ*A0)+μ n*(4*A0))/(n : ℂ)) ((Real.pi : ℂ)*(4*A0-1))
      rw [norm_div,norm_mul,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le,he0] at hsplit
      have hdiv : ‖4*(A1-τ*A0)+μ n*(4*A0)‖/‖(n : ℂ)‖≤4*‖A1-τ*A0‖+‖μ n‖*‖4*A0‖ :=
        (div_le_self (norm_nonneg _) hn1).trans hnum
      rw [hZn,he0]
      have hprod := mul_le_mul_of_nonneg_left hA0 (norm_nonneg (μ n))
      nlinarith
    have hZnBound : ‖Z‖≤M := by
      have hz := norm_add_le (((2*B : ℝ) : ℂ) • Coeff.magnitude γ+
        ((M0+1 : ℝ) : ℂ) • Coeff.magnitude μ) ((Real.pi : ℂ) • Coeff.magnitude (G0 ψ))
      have hz' := norm_add_le (((2*B : ℝ) : ℂ) • Coeff.magnitude γ)
        (((M0+1 : ℝ) : ℂ) • Coeff.magnitude μ)
      simp only [norm_smul,Coeff.norm_magnitude,Complex.norm_real,
        Real.norm_of_nonneg (by positivity : 0≤2*B),Real.norm_of_nonneg (by positivity : 0≤M0+1),
        Real.norm_of_nonneg Real.pi_pos.le] at hz hz'
      have hg := (hgap ψ (hsub hψ).2.2.1).1
      have hm := (hmid ψ (hsub hψ).2.2.2).1
      have h0 := hnorm0 ψ (hsub hψ).1.2
      apply hz.trans
      dsimp only [M]
      exact add_le_add (hz'.trans (add_le_add
        (mul_le_mul_of_nonneg_left hg (by positivity))
        (mul_le_mul_of_nonneg_left hm (by positivity))))
        (mul_le_mul_of_nonneg_left h0 Real.pi_pos.le)
    let v : Coeff 2 := ⟨f ψ,(lp.memℓp Z).mono' hpoint⟩
    exact ⟨v,fun _ => rfl,(lp.norm_mono (by norm_num) hpoint).trans hZnBound⟩
  obtain ⟨hval,hG⟩ := Coeff.analytic_realization_of_local_bounds (r := 2) f isOpen_ball hf
    (fun ψ hψ => ⟨U,isOpen_ball,hψ,Subset.refl _,M,hbounded⟩)
  refine ⟨r,hr,hUC,M,hM,(fun ψ => Coeff.ofFunctionOrZero 2 (f ψ)),hG,hval,?_⟩
  intro ψ hψ
  obtain ⟨v,hv,hvn⟩ := hbounded ψ hψ
  change ‖Coeff.ofFunctionOrZero 2 (f ψ)‖≤M
  rwa [Coeff.ofFunctionOrZero_eq_of_coordinates _ v hv]

end NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
