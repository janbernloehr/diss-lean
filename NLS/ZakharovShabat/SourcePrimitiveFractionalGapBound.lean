import NLS.ZakharovShabat.SourceCriticalFractionalQuotientDecay
import NLS.ZakharovShabat.SourceFullAbelianUniformGapComparison
import NLS.ZakharovShabat.SourceNormalizedActionUniformTailCircles
import NLS.SequenceSpaces.WeightedGapErrorAlgebra

/-! The ACTUAL Abelian primitive has a fractional relative gap error
on full complex weighted-source neighborhoods, also at collapsed gaps. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

theorem exists_local_sobolev_primitive_gap_bound
    (t : ℝ) (ht : 0≤t) (u : ℝ) (hu0 : 0≤u) (hu1 : u≤1) (hut : u≤t)
    (φ : realTypeSourceSubmodule 2) :
    let L := normalizedWeightedSourceCLM (p := 2) (sourceSobolevSpectralWeight t ht)
    ∃ T : Set (CoeffPair 2), IsOpen T ∧ φ.val∈T ∧ ∃ K : ℕ, ∃ M : ℝ, 0≤M ∧
      ∀ ψ∈T, ∀ (W : Set (CoeffPair 2))
        (C : SourceFullAbelianUniformCauchyFamily (by norm_num) (by norm_num) W),
        L ψ∈ball C.discs.source.val C.discs.sourceRadius →
        ∀ j : ℤ, K≤j.natAbs → ∀ θ∈Icc (0 : ℝ) Real.pi, ∀ upper : Bool,
          Weight.sobolev u j*‖C.gapBoundary j (L ψ) θ upper-
            I*sourceStandardRootGapBoundary (by norm_num) (by norm_num) (L ψ) j θ upper‖≤
              ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ) j‖*M := by
  intro L
  have hrφ : L φ.val∈realTypeSourceLocus 2 :=
    normalizedWeightedSource_realType (sourceSobolevSpectralWeight t ht) φ.val φ.property
  obtain ⟨Nq,εq,_hεq,Tq,hTq,hφq,Kq,hNKq,Mq,hMq,hquot⟩ :=
    exists_local_sobolev_critical_quotient_decay t ht u hu0 hu1 (by linarith) φ
  obtain ⟨Vc,hVc,hφc,A,hA,B,hB,hcomp⟩ :=
    exists_local_uniform_sourceFullAbelian_gap_comparison (by norm_num) (by norm_num) (L φ.val) hrφ
  obtain ⟨Kg,Vg,hVg,hφg,htiny⟩ :=
    exists_local_sourcePeriodicMidpointGap_tiny_tail (by norm_num) (by norm_num) (L φ.val)
  obtain ⟨G,hG,hφG,R,hR,hgap⟩ := exists_local_sobolevSquaredGap_bounds t ht φ.val
  let T := (Tq∩G)∩L ⁻¹' (Vc∩Vg)
  have hT : IsOpen T := (hTq.inter hG).inter ((hVc.inter hVg).preimage L.continuous)
  have hφT : φ.val∈T := ⟨⟨hφq,hφG⟩,hφc,hφg⟩
  let M := (A*Mq+(R+1)*B)*Real.pi
  have hM : 0≤M := by dsimp only [M];positivity
  refine ⟨T,hT,hφT,max Kq Kg,M,hM,?_⟩
  intro ψ hψ W C hψC j hj θ hθ upper
  have hjq : Kq≤j.natAbs := (le_max_left _ _).trans hj
  have hjg : Kg≤j.natAbs := (le_max_right _ _).trans hj
  let γ := sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ)
  let Q := sourceCriticalGapQuotient (by norm_num) (by norm_num) (L ψ)
  have hQ : ‖Q j‖≤B := (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞)≠0) Q j).trans
    (hcomp (L ψ) hψ.2.1).1
  have hγ : Weight.sobolev u j*‖γ j‖≤R+1 :=
    (mul_le_mul_of_nonneg_right (Weight.sobolev_mono hut j) (norm_nonneg _)).trans
      ((hgap ψ hψ.1.2).choose_spec.2.2 j)
  have he : ∀ z∈sourcePeriodicSegment (by norm_num) (by norm_num) (L ψ) j,
      ‖sourceSingleRootQuotientJointProduct (by norm_num) (by norm_num) j
        (z,(canonicalCriticalDisplacement (by norm_num) (by norm_num) (periodOnePotential (L ψ))
          (periodOnePotential_mem _),L ψ))-1‖≤Mq/Weight.sobolev u j := by
    intro z hz
    obtain ⟨hm,hg⟩ := htiny (L ψ) hψ.2.2 j hjg
    have hz8 := sourcePeriodicSegment_subset_free_eighth_ball (by norm_num) (by norm_num) (L ψ) j hm hg hz
    have hzq : z∈sourceIsolatingDisc (by norm_num) (by norm_num) (L φ.val) Nq εq j := by
      simp only [sourceIsolatingDisc,if_neg (by omega : ¬j.natAbs≤Nq)]
      exact (mem_ball.mp hz8).trans (by linarith [Real.pi_pos])
    exact (le_div_iff₀ ((Weight.sobolev u).positive j)).mpr
      (by simpa only [mul_comm] using hquot ψ hψ.1.1 j hjq z hzq)
  have hb := (hcomp (L ψ) hψ.2.1).2 W C hψC j (Mq/Weight.sobolev u j)
    (div_nonneg hMq ((Weight.sobolev u).positive j).le) he θ hθ upper
  have hw := NLS.weighted_primitive_gap_error_bound (Weight.sobolev u j) ‖γ j‖ ‖Q j‖
    A Mq (R+1) B Real.pi _ ((Weight.sobolev u).positive j) (norm_nonneg _) (norm_nonneg _)
    Real.pi_pos.le hγ hQ hb
  simpa only [M,mul_assoc] using hw

end NLS.ZakharovShabat
