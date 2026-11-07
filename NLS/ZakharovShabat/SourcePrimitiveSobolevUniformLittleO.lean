import NLS.ZakharovShabat.SourcePrimitiveFractionalGapBound
import NLS.ZakharovShabat.SourceSobolevCriticalQuotientUniformTail
import NLS.SequenceSpaces.SobolevRatioTail

/-! # Uniform little-o for the actual Abelian primitive

For 0 < t < 1 the relative primitive error is uniformly o(⟨j⟩⁻ᵗ)
on one full complex normalized Sobolev neighborhood. All compatible
Cauchy charts, both gap sides, and collapsed gaps are included.
-/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

theorem exists_local_sobolev_primitive_gap_uniform_littleO
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1) (φ : realTypeSourceSubmodule 2) :
    let L := normalizedWeightedSourceCLM (p := 2) (sourceSobolevSpectralWeight t ht.le)
    ∃ T : Set (CoeffPair 2), IsOpen T ∧ φ.val ∈ T ∧
      ∀ ε > (0:ℝ), ∃ K : ℕ, ∀ ψ ∈ T, ∀ (W : Set (CoeffPair 2))
        (C : SourceFullAbelianUniformCauchyFamily (by norm_num) (by norm_num) W),
        L ψ ∈ ball C.discs.source.val C.discs.sourceRadius →
        ∀ j : ℤ, K ≤ j.natAbs → ∀ θ ∈ Icc (0:ℝ) Real.pi, ∀ upper : Bool,
          Weight.sobolev t j * ‖C.gapBoundary j (L ψ) θ upper -
            I*sourceStandardRootGapBoundary (by norm_num) (by norm_num) (L ψ) j θ upper‖ ≤
              ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ) j‖*ε := by
  intro L
  let u := min 1 (2*t)
  have htu : t < u := lt_min ht1 (by linarith)
  have hu0 : 0 ≤ u := ht.le.trans htu.le
  have hrφ : L φ.val ∈ realTypeSourceLocus 2 :=
    normalizedWeightedSource_realType (sourceSobolevSpectralWeight t ht.le) φ.val φ.property
  obtain ⟨Nq,εq,_,Tq,hTq,hφq,Kq,hNKq,Mq,hMq,hquot⟩ :=
    exists_local_sobolev_critical_quotient_decay t ht.le u hu0 (min_le_left _ _) (min_le_right _ _) φ
  obtain ⟨TQ,hTQ,hφQ,hQtail⟩ := exists_local_sobolev_sourceCriticalGapQuotient_uniform_tail
    (by norm_num) (by norm_num) t ht φ.val φ.property
  obtain ⟨Vc,hVc,hφc,A,hA,_B,_hB,hcomp⟩ :=
    exists_local_uniform_sourceFullAbelian_gap_comparison (by norm_num) (by norm_num) (L φ.val) hrφ
  obtain ⟨Kg,Vg,hVg,hφg,htiny⟩ :=
    exists_local_sourcePeriodicMidpointGap_tiny_tail (by norm_num) (by norm_num) (L φ.val)
  obtain ⟨G,hG,hφG,R,hR,hgap⟩ := exists_local_sobolevSquaredGap_bounds t ht.le φ.val
  let T := ((Tq ∩ TQ) ∩ G) ∩ L ⁻¹' (Vc ∩ Vg)
  have hT : IsOpen T := ((hTq.inter hTQ).inter hG).inter ((hVc.inter hVg).preimage L.continuous)
  refine ⟨T,hT,⟨⟨⟨hφq,hφQ⟩,hφG⟩,hφc,hφg⟩,?_⟩
  intro ε hε
  let δ := ε/((A+R+1)*Real.pi)
  have hden : 0 < (A+R+1)*Real.pi := mul_pos (by linarith) Real.pi_pos
  have hδ : 0 < δ := div_pos hε hden
  obtain ⟨KQ,hKQ⟩ := hQtail δ hδ
  obtain ⟨Kr,hKr⟩ := Weight.exists_sobolev_ratio_tail t u htu (div_pos hδ (by linarith : 0 < Mq+1))
  refine ⟨max (max Kq Kg) (max KQ Kr),?_⟩
  intro ψ hψ W C hψC j hj θ hθ upper
  have hjq : Kq ≤ j.natAbs := (le_max_left Kq Kg).trans ((le_max_left _ _).trans hj)
  have hjg : Kg ≤ j.natAbs := (le_max_right Kq Kg).trans ((le_max_left _ _).trans hj)
  have hjQ : KQ ≤ j.natAbs := (le_max_left KQ Kr).trans ((le_max_right _ _).trans hj)
  have hjr : Kr ≤ j.natAbs := (le_max_right KQ Kr).trans ((le_max_right _ _).trans hj)
  let γ := sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ)
  let Q := sourceCriticalGapQuotient (by norm_num) (by norm_num) (L ψ)
  have hQ : ‖Q j‖ ≤ δ := (hKQ ψ hψ.1.1.2 j hjQ).le
  have hγ : Weight.sobolev t j*‖γ j‖ ≤ R+1 := (hgap ψ hψ.1.2).choose_spec.2.2 j
  have hratio : Mq*(Weight.sobolev t j / Weight.sobolev u j) ≤ δ := by
    calc
      _ ≤ Mq*(δ/(Mq+1)) := mul_le_mul_of_nonneg_left (hKr j hjr).le hMq
      _ ≤ δ := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (by linarith : 0 < Mq+1)).mpr
        nlinarith
  have he : ∀ z ∈ sourcePeriodicSegment (by norm_num) (by norm_num) (L ψ) j,
      ‖sourceSingleRootQuotientJointProduct (by norm_num) (by norm_num) j
        (z,(canonicalCriticalDisplacement (by norm_num) (by norm_num) (periodOnePotential (L ψ))
          (periodOnePotential_mem _),L ψ))-1‖ ≤ δ/Weight.sobolev t j := by
    intro z hz
    obtain ⟨hm,hg⟩ := htiny (L ψ) hψ.2.2 j hjg
    have hz8 := sourcePeriodicSegment_subset_free_eighth_ball (by norm_num) (by norm_num) (L ψ) j hm hg hz
    have hzq : z ∈ sourceIsolatingDisc (by norm_num) (by norm_num) (L φ.val) Nq εq j := by
      simp only [sourceIsolatingDisc,if_neg (by omega : ¬j.natAbs ≤ Nq)]
      exact (mem_ball.mp hz8).trans (by linarith [Real.pi_pos])
    have hsmall := hquot ψ hψ.1.1.1 j hjq z hzq
    apply (le_div_iff₀ ((Weight.sobolev t).positive j)).mpr
    calc
      _ ≤ (Mq/Weight.sobolev u j)*Weight.sobolev t j :=
        mul_le_mul_of_nonneg_right ((le_div_iff₀ ((Weight.sobolev u).positive j)).mpr
          (by simpa only [mul_comm] using hsmall)) ((Weight.sobolev t).positive j).le
      _ ≤ δ := by simpa only [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hratio
  have hb := (hcomp (L ψ) hψ.2.1).2 W C hψC j (δ/Weight.sobolev t j)
    (div_nonneg hδ.le ((Weight.sobolev t).positive j).le) he θ hθ upper
  have hw := NLS.weighted_primitive_gap_error_bound (Weight.sobolev t j) ‖γ j‖ ‖Q j‖
    A δ (R+1) δ Real.pi _ ((Weight.sobolev t).positive j) (norm_nonneg _) (norm_nonneg _)
    Real.pi_pos.le hγ hQ hb
  have heδ : (A*δ+(R+1)*δ)*Real.pi = ε := by
    calc
      _ = δ*((A+R+1)*Real.pi) := by ring
      _ = ε := div_mul_cancel₀ ε hden.ne'
  calc
    _ ≤ ‖γ j‖*(A*δ+(R+1)*δ)*Real.pi := hw
    _ = ‖γ j‖*ε := by rw [mul_assoc,heδ]

end NLS.ZakharovShabat
