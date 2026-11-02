import NLS.ZakharovShabat.SourcePsiCriticalFilledTail
import NLS.ZakharovShabat.SourceCriticalTailSeparation
import NLS.ZakharovShabat.SourceCriticalRootGapUniformBound

/-! # Uniform smallness of the actual root-comparison numerator

The numerator in (36) is the critical-filled quotient times a separated
critical-root ratio. Uniform quotient tails and uniformly small periodic
gaps make it close to one simultaneously for every deleted index.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The literal numerator ξ in the root-comparison normalizing period. -/
def sourcePsiCriticalNormalizer (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n k : ℤ) (a : DeletedCoeff p n) (ψ : CoeffPair p) (z : ℂ) : ℂ :=
  ((sourceCriticalRoot hp hp1 ψ n-sourceCriticalRoot hp hp1 ψ k)/
    (sourceCriticalRoot hp hp1 ψ n-z))*sourcePsiCriticalFilledQuotient hp hp1 n k a ψ z

/-- Splitting off the unit numerator ratio gives a direct complex norm bound. -/
theorem norm_root_ratio_mul_sub_one_le (nu rho z zeta : ℂ) (hnu : nu-z ≠ 0) :
    ‖((nu-rho)/(nu-z))*zeta-1‖ ≤ ‖zeta-1‖+‖z-rho‖/‖nu-z‖*‖zeta‖ := by
  have he : ((nu-rho)/(nu-z))*zeta-1 = (zeta-1)+((z-rho)/(nu-z))*zeta := by
    field_simp [hnu]
    ring
  rw [he]
  exact (norm_add_le _ _).trans_eq (by rw [norm_mul,norm_div])

/-- One complex neighborhood and selected-index cutoff give gap smallness
of the actual numerator, uniformly in the deleted index. -/
theorem SourceLemma12_11Data.exists_local_critical_normalizer_small_tail
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (H : SourceLemma12_11Data hp hp1 W₀ W s)
    (φ : realTypeSourceLocus p) (hφ : φ.val ∈ W) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ.val ∈ V ∧ V ⊆ W ∧ ∃ K : ℕ,
      ∀ ψ ∈ V, ∀ n k : ℤ, K ≤ k.natAbs → k ≠ n →
        ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k,
          ‖sourcePsiCriticalNormalizer hp hp1 n k (s n ψ) ψ z-1‖ ≤ 1/2 := by
  obtain ⟨Vq,hVq,hφq,hVqW,Kq,hq⟩ :=
    H.exists_local_critical_filled_quotient_small_tail φ hφ (1/4) (by norm_num)
  obtain ⟨Vd,hVd,hφd,B,hB,hd⟩ :=
    exists_local_uniform_sourceCriticalPoint_gap_distance_bound hp hp1 φ.val φ.property
  obtain ⟨Vs,hVs,hφs,Ks,hs⟩ := exists_local_sourceCritical_tail_lattice_separation hp hp1 φ
  let δ := Real.pi/(32*B)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨N,_,Vg,hVg,hφg,_,_,hg⟩ :=
    exists_uniform_small_sourcePeriodicGapDisplacement hp hp1 φ.val hδ
  let V := (Vq ∩ Vd) ∩ (Vs ∩ Vg)
  refine ⟨V,(hVq.inter hVd).inter (hVs.inter hVg),⟨⟨hφq,hφd⟩,hφs,hφg⟩,
    fun _ h => hVqW h.1.1,max Kq (max Ks (N+1)),?_⟩
  intro ψ hψ n k hk hkn z hz
  have hkq : Kq ≤ k.natAbs := (le_max_left _ _).trans hk
  have hks : Ks ≤ k.natAbs := (le_max_left _ _).trans ((le_max_right _ _).trans hk)
  have hNk : N < k.natAbs := by omega
  obtain ⟨hseg,hquot⟩ := hq ψ hψ.1.1 n k hkq
  have hzB := ball_subset_closedBall (hseg hz)
  have hden := hs ψ hψ.2.1 k hks n hkn.symm z hzB
  have habs : 1 ≤ |((n-k : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hkn.symm)
  have hden' : Real.pi/2 ≤ ‖sourceCriticalRoot hp hp1 ψ n-z‖ := by
    nlinarith [Real.pi_pos]
  have hden0 : sourceCriticalRoot hp hp1 ψ n-z ≠ 0 :=
    norm_pos_iff.mp ((by positivity : (0:ℝ)<Real.pi/2).trans_le hden')
  have hnot : k ∉ Finset.Icc (-(N:ℤ)) N := by simp only [Finset.mem_Icc]; omega
  have hgap : ‖sourcePeriodicGapDisplacement hp hp1 ψ k‖ ≤ δ := by
    have ht := (lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne'
      (sourcePeriodicGapDisplacement hp hp1 ψ-
        Coeff.truncate (Finset.Icc (-(N:ℤ)) N) (sourcePeriodicGapDisplacement hp hp1 ψ)) k).trans
        ((hg ψ hψ.2.2).2 N le_rfl)
    simpa only [lp.coeFn_sub,Pi.sub_apply,Coeff.truncate_apply,if_neg hnot,sub_zero] using ht
  have hδeq : B*δ = Real.pi/32 := by dsimp [δ]; field_simp
  have hnum : ‖z-sourceCriticalRoot hp hp1 ψ k‖ ≤ Real.pi/32 := by
    have h := (hd ψ hψ.1.2 k z hz).trans (mul_le_mul_of_nonneg_left hgap hB.le)
    rw [hδeq,norm_sub_rev] at h
    exact h
  have hratio : ‖z-sourceCriticalRoot hp hp1 ψ k‖/‖sourceCriticalRoot hp hp1 ψ n-z‖ ≤ 1/16 := by
    apply (div_le_iff₀ (norm_pos_iff.mpr hden0)).mpr
    nlinarith
  have herr := (hquot z hzB).le
  have hnorm : ‖sourcePsiCriticalFilledQuotient hp hp1 n k (s n ψ) ψ z‖ ≤ 5/4 := by
    have ht := norm_sub_le_norm_sub_add_norm_sub
      (sourcePsiCriticalFilledQuotient hp hp1 n k (s n ψ) ψ z) 1 0
    simp only [sub_zero,norm_one] at ht
    linarith
  apply (norm_root_ratio_mul_sub_one_le _ _ _ _ hden0).trans
  have hmul := mul_le_mul hratio hnorm (norm_nonneg _) (by norm_num : (0:ℝ)≤1/16)
  linarith

end NLS.ZakharovShabat
