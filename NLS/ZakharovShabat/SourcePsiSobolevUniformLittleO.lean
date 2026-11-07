import NLS.ZakharovShabat.SourcePsiFractionalQuotientDecay
import NLS.ZakharovShabat.SourceNormalizedActionUniformTailCircles
import NLS.SequenceSpaces.SobolevRatioTail

/-! Uniform little-o for the actual filled-psi quotient on whole gaps,
on one fixed complex Sobolev neighborhood and before all omitted labels. -/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {V : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

theorem SourcePsiSquaredGapComplexExtension.exists_local_sobolev_filled_quotient_uniform_littleO
    (hs : SourcePsiSquaredGapComplexExtension (by norm_num) (by norm_num) V s)
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1) (φ : realTypeSourceSubmodule 2)
    (hφV : normalizedWeightedSourceCLM (p := 2) (sourceSobolevSpectralWeight t ht.le) φ.val ∈ V) :
    let L := normalizedWeightedSourceCLM (p := 2) (sourceSobolevSpectralWeight t ht.le)
    ∃ T : Set (CoeffPair 2), IsOpen T ∧ φ.val ∈ T ∧ T ⊆ L ⁻¹' V ∧
      ∀ ε > (0:ℝ), ∃ K : ℕ, ∀ ψ ∈ T, ∀ n k : ℤ, K ≤ k.natAbs →
        ∀ z ∈ sourcePeriodicSegment (by norm_num) (by norm_num) (L ψ) k,
          Weight.sobolev t k * ‖sourceSingleRootQuotientJointProduct (by norm_num) (by norm_num) k
            (z,(sourcePsiFillDeletedRoot n (s n (L ψ))
              (sourceStandardRootMidpoint (by norm_num) (by norm_num) (L ψ) n),L ψ))-1‖ ≤ ε := by
  intro L
  let u := min 1 (2*t)
  have htu : t < u := lt_min ht1 (by linarith)
  obtain ⟨Nq,εq,_,Tq,hTq,hφq,hqV,Kq,hNKq,Mq,hMq,hquot⟩ :=
    hs.exists_local_sobolev_filled_quotient_decay t ht.le u (ht.le.trans htu.le)
      (min_le_left _ _) (min_le_right _ _) φ hφV
  obtain ⟨Kg,Vg,hVg,hφg,htiny⟩ :=
    exists_local_sourcePeriodicMidpointGap_tiny_tail (by norm_num) (by norm_num) (L φ.val)
  refine ⟨Tq ∩ L ⁻¹' Vg,hTq.inter (hVg.preimage L.continuous),⟨hφq,hφg⟩,
    (fun _ hψ => hqV hψ.1),?_⟩
  intro ε hε
  obtain ⟨Kr,hKr⟩ := Weight.exists_sobolev_ratio_tail t u htu (div_pos hε (by linarith : 0 < Mq+1))
  refine ⟨max Kq (max Kg Kr),?_⟩
  intro ψ hψ n k hk z hz
  have hkq : Kq ≤ k.natAbs := (le_max_left _ _).trans hk
  have hkg : Kg ≤ k.natAbs := (le_max_left _ _).trans ((le_max_right _ _).trans hk)
  have hkr : Kr ≤ k.natAbs := (le_max_right _ _).trans ((le_max_right _ _).trans hk)
  obtain ⟨hm,hg⟩ := htiny (L ψ) hψ.2 k hkg
  have hz8 := sourcePeriodicSegment_subset_free_eighth_ball (by norm_num) (by norm_num) (L ψ) k hm hg hz
  have hzq : z ∈ sourceIsolatingDisc (by norm_num) (by norm_num) (L φ.val) Nq εq k := by
    simp only [sourceIsolatingDisc,if_neg (by omega : ¬k.natAbs ≤ Nq)]
    exact (mem_ball.mp hz8).trans (by linarith [Real.pi_pos])
  have hb := hquot ψ hψ.1 n k hkq z hzq
  have hratio : Mq*(Weight.sobolev t k / Weight.sobolev u k) ≤ ε := by
    calc
      _ ≤ Mq*(ε/(Mq+1)) := mul_le_mul_of_nonneg_left (hKr k hkr).le hMq
      _ ≤ ε := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (by linarith : 0 < Mq+1)).mpr
        nlinarith
  calc
    _ ≤ Weight.sobolev t k*(Mq/Weight.sobolev u k) :=
      mul_le_mul_of_nonneg_left ((le_div_iff₀ ((Weight.sobolev u).positive k)).mpr
        (by simpa only [mul_comm] using hb)) ((Weight.sobolev t).positive k).le
    _ ≤ ε := by simpa only [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hratio

end NLS.ZakharovShabat
