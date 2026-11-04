import NLS.ZakharovShabat.SourcePsiCriticalRootBound
import NLS.ZakharovShabat.SourcePsiCriticalInitialOffset
import NLS.ZakharovShabat.SourceCriticalRelativeRowBound

/-! # The actual root bootstrap inequality on a common source neighborhood

All constants and spectral hypotheses are constructed near each real
source. The output retains the literal absolute reciprocal row in the
actual critical-filled root difference, with a quadratic gap remainder.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual gap-normalized root difference satisfies the reciprocal-row
bootstrap inequality, uniformly in both indices on one complex neighborhood. -/
theorem SourceLemma12_11Data.exists_local_critical_reciprocal_inequality
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (H : SourceLemma12_11Data hp hp1 W₀ W s)
    (φ : realTypeSourceLocus p) (hφ : φ.val ∈ W) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ.val ∈ V ∧ V ⊆ W ∧
      ∃ K : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ V, ∀ n k : ℤ, K ≤ k.natAbs →
        ‖sourcePsiCriticalGapNormalized hp hp1 s n ψ k‖ ≤ C*
          ((∑' m, ‖sourcePsiCriticalDifference hp hp1 s n ψ m‖*‖NLS.Fourier.hilbertKernel (k-m)‖)+
            ‖sourcePeriodicGapDisplacement hp hp1 ψ k‖*‖NLS.Fourier.hilbertKernel (n-k)‖) := by
  obtain ⟨Vp,hVp,hφp,hVpW,Kp,cp,_,hpcontrol⟩ :=
    H.exists_local_critical_comparison_period_lower_bound φ hφ
  obtain ⟨Vl,hVl,hφl,_,L,hL,hl⟩ := H.exists_local_uniform_critical_filled_difference_norm_bound φ hφ
  obtain ⟨Vq,hVq,hφq,_,Kq,hq⟩ := H.exists_local_critical_filled_quotient_small_tail φ hφ 1 (by norm_num)
  obtain ⟨Vm,hVm,hφm,Km,M,hM,hm⟩ :=
    exists_local_uniform_sourceCriticalRootRatioExtension_tail_bound hp hp1 φ.val φ.property
  obtain ⟨Vb,hVb,hφb,B,hB,hb⟩ :=
    exists_local_uniform_sourceCriticalPoint_gap_distance_bound hp hp1 φ.val φ.property
  obtain ⟨Vs,hVs,hφs,Ks,hs⟩ := exists_local_sourceCritical_tail_lattice_separation hp hp1 φ
  obtain ⟨I,_,_,hrealI,hisol⟩ := sourceLemma10_1 hp hp1
  obtain ⟨Vd,hVd,_,hφd,_,χ,_,N,ε,_,_,c,hD⟩ := hisol φ.val (hrealI φ.property)
  let V := Vp ∩ Vl ∩ Vq ∩ Vm ∩ Vb ∩ Vs ∩ Vd
  let κ := ‖Coeff.puncturedLattice p.conjExponent
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)‖
  let A := M*Real.exp (c*L*κ)*c
  let C := 2*B*A+8*B^2/Real.pi
  have hc : 0 < c := zero_lt_one.trans_le hD.one_le
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨V,(((((hVp.inter hVl).inter hVq).inter hVm).inter hVb).inter hVs).inter hVd,
    ⟨⟨⟨⟨⟨⟨hφp,hφl⟩,hφq⟩,hφm⟩,hφb⟩,hφs⟩,hφd⟩,
    fun _ h => hVpW h.1.1.1.1.1.1,max Kp (max Kq (max Km Ks)),C,hC,?_⟩
  intro ψ hψ n k hk
  rcases hψ with ⟨⟨⟨⟨⟨⟨hψp,hψl⟩,hψq⟩,hψm⟩,hψb⟩,hψs⟩,hψd⟩
  by_cases hkn : k=n
  · subst k
    simp only [sourcePsiCriticalGapNormalized,sourcePsiCriticalDifference_same,zero_div,norm_zero]
    positivity
  by_cases hγ : sourcePeriodicGapDisplacement hp hp1 ψ k = 0
  · simp only [sourcePsiCriticalGapNormalized,hγ,div_zero,norm_zero]
    positivity
  have hγpos : 0 < ‖sourcePeriodicGapDisplacement hp hp1 ψ k‖ := norm_pos_iff.mpr hγ
  have hkp : Kp ≤ k.natAbs := by omega
  have hkq : Kq ≤ k.natAbs := by omega
  have hkm : Km ≤ k.natAbs := by omega
  have hks : Ks ≤ k.natAbs := by omega
  obtain ⟨hseg,hquot⟩ := hq ψ hψq n k hkq
  let δ := sourcePsiCriticalDifference hp hp1 s n ψ
  let T := ∑' m, ‖δ m‖*‖NLS.Fourier.hilbertKernel (k-m)‖
  have hT : 0 ≤ T := tsum_nonneg (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hdist : 0 < |((n-k : ℤ) : ℝ)| := by
    exact_mod_cast abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hkn))
  have hd : 0 < (Real.pi/2)*|((n-k : ℤ) : ℝ)| := mul_pos (by positivity) hdist
  have herror (z : ℂ) (hz : z ∈ sourcePeriodicSegment hp hp1 ψ k) :
      ‖sourcePsiCriticalFilledQuotient hp hp1 n k (s n ψ) ψ z-
        sourceCriticalDeletedQuotient hp hp1 k ψ z‖ ≤ A*T := by
    have hzq : z ∈ ball ((Real.pi:ℂ)*k) (Real.pi/4) :=
      ball_subset_ball (by linarith [Real.pi_pos]) (hseg hz)
    have hχ : ‖sourceCriticalDeletedQuotient hp hp1 k ψ z‖ ≤ M := by
      simpa only [sourceCriticalRootRatioExtension,norm_mul,norm_neg,norm_I,one_mul,
        sourceCriticalDeletedQuotient] using hm ψ hψm k hkm z hzq
    exact hD.norm_quotient_sub_critical_le_reciprocalRow ψ hψd k
      (sourcePsiFillDeletedRoot n (s n ψ) (sourceCriticalRoot hp hp1 ψ n)) z
      (subset_closure (hD.gap ψ hψd k hz)) M L hχ (hl ψ hψl n)
  have hprod (z : ℂ) (hz : z ∈ sourcePeriodicSegment hp hp1 ψ k) :
      ‖sourcePsiCriticalFilledQuotient hp hp1 n k (s n ψ) ψ z‖ ≤ 2 := by
    have he := hquot z (ball_subset_closedBall (hseg hz))
    have ht := norm_sub_le_norm_sub_add_norm_sub
      (sourcePsiCriticalFilledQuotient hp hp1 n k (s n ψ) ψ z) 1 0
    simp only [sub_zero,norm_one] at ht
    linarith
  have hden (z : ℂ) (hz : z ∈ sourcePeriodicSegment hp hp1 ψ k) :
      (Real.pi/2)*|((n-k : ℤ) : ℝ)| ≤ ‖sourceCriticalRoot hp hp1 ψ n-z‖ :=
    hs ψ hψs k hks n (Ne.symm hkn) z (ball_subset_closedBall (hseg hz))
  have hroot := (hpcontrol ψ hψp n k hkp hkn).root_difference_le
    (B*‖sourcePeriodicGapDisplacement hp hp1 ψ k‖) (A*T) 2
    ((Real.pi/2)*|((n-k : ℤ) : ℝ)|) (mul_nonneg hB.le (norm_nonneg _)) hd
    (fun z hz => by simpa only [sourceCriticalRoot,norm_sub_rev] using hb ψ hψb k z hz)
    herror hprod hden
  have hkernel : ‖NLS.Fourier.hilbertKernel (n-k)‖ = |((n-k : ℤ) : ℝ)|⁻¹ := by
    rw [NLS.Fourier.hilbertKernel,norm_neg,norm_inv,Complex.norm_intCast]
  have hid : 2*(B*‖sourcePeriodicGapDisplacement hp hp1 ψ k‖*(A*T)+
      (B*‖sourcePeriodicGapDisplacement hp hp1 ψ k‖)^2*2/((Real.pi/2)*|((n-k : ℤ) : ℝ)|)) =
      ‖sourcePeriodicGapDisplacement hp hp1 ψ k‖*
        (2*B*A*T+(8*B^2/Real.pi)*
          (‖sourcePeriodicGapDisplacement hp hp1 ψ k‖*|((n-k : ℤ) : ℝ)|⁻¹)) := by
    field_simp
    ring
  have hroot' : ‖sourcePsiCriticalDifference hp hp1 s n ψ k‖ ≤
      ‖sourcePeriodicGapDisplacement hp hp1 ψ k‖*(C*
        (T+‖sourcePeriodicGapDisplacement hp hp1 ψ k‖*‖NLS.Fourier.hilbertKernel (n-k)‖)) := by
    rw [sourcePsiCriticalDifference_other hp hp1 s n k hkn]
    apply hroot.trans
    rw [hid,hkernel]
    apply mul_le_mul_of_nonneg_left _ hγpos.le
    dsimp only [C]
    nlinarith [mul_nonneg (by positivity : 0 ≤ 2*B*A)
      (mul_nonneg (norm_nonneg (sourcePeriodicGapDisplacement hp hp1 ψ k)) (inv_nonneg.mpr hdist.le)),
      mul_nonneg (by positivity : 0 ≤ 8*B^2/Real.pi) hT]
  unfold sourcePsiCriticalGapNormalized
  rw [norm_div]
  exact (div_le_iff₀ hγpos).mpr (by
    dsimp only [T,δ] at hroot'
    simpa only [mul_comm] using hroot')

end NLS.ZakharovShabat
