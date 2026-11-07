import NLS.ZakharovShabat.SourceHigherActionOneCenteredTail
import NLS.ZakharovShabat.SourceNormalizedActionComplexSobolevDecay

/-! Quantitative one-order decay of the EXACT filled Miura action
ratio on complex H1 source neighborhoods. The first higher action,
periodic midpoint and free pi*n normalization are retained. -/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

private theorem normalized_moment_ratio_bound (F Q τ c : ℂ) (n C K : ℝ)
    (hn : 1 ≤ n) (hC : 0 ≤ C) (hc : ‖c‖ = Real.pi*n)
    (hτ : ‖τ-c‖ ≤ Real.pi/8) (hF : ‖F-τ*Q‖ ≤ C)
    (hQ : (1+n)*‖4*Q-1‖ ≤ K) :
    (1+n)*‖4*c*F/τ^2-1‖ ≤ 32*C/Real.pi+2*K+1/2 := by
  let p := Real.pi*n
  have hp : 0 < p := mul_pos Real.pi_pos (by linarith)
  have ht : p/2 ≤ ‖τ‖ := by
    have hh := norm_add_le (c-τ) τ
    rw [sub_add_cancel,hc,norm_sub_rev] at hh
    dsimp only [p]
    nlinarith [Real.pi_pos]
  have ht0 : 0 < ‖τ‖ := (by positivity : 0 < p/2).trans_le ht
  have hτ0 : τ ≠ 0 := norm_pos_iff.mp ht0
  have he : 4*c*F/τ^2-1 =
      (4*c*(F-τ*Q))/τ^2+(c/τ)*(4*Q-1)+(c-τ)/τ := by
    field_simp
    ring
  have hfirst : ‖(4*c*(F-τ*Q))/τ^2‖ ≤ 16*C/p := by
    rw [norm_div,norm_mul,norm_mul,norm_pow,hc,Complex.norm_ofNat]
    change 4*p*‖F-τ*Q‖/‖τ‖^2 ≤ _
    calc
      _ ≤ 4*p*C/(p/2)^2 := by gcongr
      _ = _ := by field_simp; ring
  have hsecond : ‖(c/τ)*(4*Q-1)‖ ≤ 2*‖4*Q-1‖ := by
    rw [norm_mul,norm_div,hc]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    change p/‖τ‖ ≤ 2
    exact (div_le_iff₀ ht0).mpr (by linarith)
  have hthird : ‖(c-τ)/τ‖ ≤ (Real.pi/4)/p := by
    rw [norm_div,norm_sub_rev]
    calc
      _ ≤ (Real.pi/8)/(p/2) := div_le_div₀ (by positivity) hτ (by positivity) ht
      _ = _ := by field_simp; norm_num
  have hnorm : ‖4*c*F/τ^2-1‖ ≤ 16*C/p+2*‖4*Q-1‖+(Real.pi/4)/p := by
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add hfirst hsecond)) hthird)
  have hratio : (1+n)/p ≤ 2/Real.pi := by
    apply (div_le_div_iff₀ hp Real.pi_pos).mpr
    dsimp only [p]
    nlinarith [Real.pi_pos]
  calc
    _ ≤ (1+n)*(16*C/p+2*‖4*Q-1‖+(Real.pi/4)/p) :=
      mul_le_mul_of_nonneg_left hnorm (by linarith)
    _ = (16*C)*((1+n)/p)+2*((1+n)*‖4*Q-1‖)+(Real.pi/4)*((1+n)/p) := by ring
    _ ≤ (16*C)*(2/Real.pi)+2*K+(Real.pi/4)*(2/Real.pi) := by gcongr
    _ = _ := by field_simp; ring

theorem exists_local_normalizedSobolevHigherActionOneRatio_decay (φ : realTypeSourceLocus 2) :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ φ.val ∈ U ∧ ∃ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ ψ ∈ U, ∀ n : ℕ+, N ≤ (n:ℕ) →
        let χ := normalizedWeightedSource (SpectralWeight.sobolev 1 (by norm_num)) ψ
        (1+(n:ℝ))*‖(4*((Real.pi:ℂ)*(n:ℕ)))*
            sourceHigherActionOneNormalized (by simp) (by norm_num) (n:ℕ) χ /
              (sourceStandardRootMidpoint (by simp) (by norm_num) χ (n:ℕ))^2-1‖ ≤ C := by
  let w := SpectralWeight.sobolev 1 (by norm_num)
  let L := normalizedWeightedSourceCLM (p := 2) w
  let φu := L φ.val
  have hr : IsRealType (CoeffPair.toMax 2 φu) := normalizedWeightedSource_realType w φ.val φ.property
  obtain ⟨Va,hVa,hφVa,K,hK,ha⟩ := exists_local_normalizedSobolevActionDeviation_decay φ
  obtain ⟨Vf,hVf,hφVf,Nf,F,hF,hcenter⟩ :=
    exists_local_sourceHigherActionOneNormalized_centered_tail_bound φu hr
  obtain ⟨Ng,Vg,hVg,hφVg,hgeom⟩ :=
    exists_local_sourceNormalizedAction_uniform_tail_circle_data (by simp) (by norm_num) φu hr
  let U := Va ∩ L ⁻¹' (Vf ∩ Vg)
  refine ⟨U,hVa.inter ((hVf.inter hVg).preimage L.continuous),⟨hφVa,hφVf,hφVg⟩,
    max Nf Ng,32*F/Real.pi+2*K+1/2,by positivity,?_⟩
  intro ψ hψ n hn
  have hnF : Nf ≤ (((n:ℕ):ℤ)).natAbs := by simpa only [Int.natAbs_natCast] using (le_max_left Nf Ng).trans hn
  have hnG : Ng ≤ (((n:ℕ):ℤ)).natAbs := by simpa only [Int.natAbs_natCast] using (le_max_right Nf Ng).trans hn
  have hmid := (hgeom (L ψ) hψ.2.2 (n:ℕ) hnG).1
    (sourcePeriodicMidpoint_mem_segment (by simp) (by norm_num) (L ψ) (n:ℕ))
  have hmidnorm : ‖sourceStandardRootMidpoint (by simp) (by norm_num) (L ψ) (n:ℕ)-
      ((Real.pi:ℂ)*(n:ℕ))‖ ≤ Real.pi/8 := by
    simpa only [dist_eq_norm,Int.cast_natCast] using (mem_ball.mp hmid).le
  have hnR : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr n.ne_zero
  have hc : ‖((Real.pi:ℂ)*(n:ℕ))‖ = Real.pi*(n:ℝ) := by
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le,Complex.norm_natCast]
  have hq : (1+(n:ℝ))*‖4*sourceNormalizedActionComplexExtension (by simp) (by norm_num)
      (n:ℕ) (L ψ)-1‖ ≤ K := by
    simpa only [L,w,normalizedWeightedSourceCLM_apply,sourceNormalizedActionDeviation,Int.cast_natCast,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ))]
      using ha ψ hψ.1 (n:ℕ)
  exact normalized_moment_ratio_bound _ _ _ _ (n:ℝ) F K hnR hF hc hmidnorm
    (hcenter (L ψ) hψ.2.1 (n:ℕ) hnF) hq

end NLS.ZakharovShabat
