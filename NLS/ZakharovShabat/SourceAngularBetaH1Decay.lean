import NLS.SequenceSpaces.WeightedReciprocalDecay
import NLS.ZakharovShabat.SourceAngularBetaCorrectionBound
import NLS.ZakharovShabat.SourceAbelianMomentSquaredOffsetError
import NLS.ZakharovShabat.SourceWeightedGapSequence
import NLS.ZakharovShabat.SourceSobolevFiniteGapDensity

/-! # Locally uniform H1 decay of the actual beta corrections

Real Dirichlet interlacing bounds the midpoint displacement by half the
periodic gap. The weighted Hilbert gap sequence then controls the actual
infinite angular sum. The original root family is retained, and the H1
neighborhood estimate requires no finite-gap hypothesis.
-/

noncomputable section

namespace NLS.ZakharovShabat
open Set Metric Complex Filter Topology
open scoped ENNReal

/-- Real interlacing controls the Dirichlet-to-midpoint term by half the actual gap. -/
theorem norm_sourceDirichletMidpointDisplacement_le_half_gap
    (φ : realTypeSourceSubmodule 2) (m : ℤ) :
    ‖sourceDirichletMidpointDisplacement (by simp) (by norm_num) φ.val m‖ ≤
      ‖sourcePeriodicGapDisplacement (by simp) (by norm_num) φ.val m‖/2 := by
  rw [sourceDirichletMidpointDisplacement_apply,norm_sub_rev]
  exact norm_sourceMidpoint_sub_le_halfGap (by simp) (by norm_num) φ.val m _
    (canonicalPeriodOneBoundaryRoots_mem_sourcePeriodicSegment_of_realType
      (by simp) (by norm_num) .dirichlet φ.val φ.property m)

/-- The actual angle series has inverse-bracket decay whenever the actual gaps have a Hilbert derivative. -/
theorem sourceAngularBetaCorrection_weighted_bound
    (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n)
    (φ : realTypeSourceSubmodule 2) (G : Coeff 2)
    (hG : ∀ m : ℤ, (1+|(m:ℝ)|)*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) φ.val m‖ ≤ ‖G m‖)
    (C : ℝ) (hC : 0 ≤ C)
    (hbeta : ∀ n m : ℤ, m ≠ n →
      ‖sourceAngularBeta (by simp) (by norm_num) n m s φ.val‖ ≤ C *
        (‖sourcePeriodicGapDisplacement (by simp) (by norm_num) φ.val m‖ +
          ‖canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet φ.val m -
            sourceStandardRootMidpoint (by simp) (by norm_num) φ.val m‖) / |((n-m:ℤ):ℝ)|)
    (n : ℤ) :
    (1+|(n:ℝ)|)*‖sourceAngularBetaCorrection (by simp) (by norm_num) n s φ.val‖ ≤ 6*C*‖G‖ := by
  have hu (m : ℤ) :
      ‖sourceAngularBetaSeriesTerm (by simp) (by norm_num) n s φ.val m‖ ≤
        ((3/2:ℝ)*C)*‖G m‖/(1+|(m:ℝ)|)*
          ‖Coeff.shift n (Coeff.puncturedLattice 2 (by norm_num)) m‖ := by
    rw [Coeff.norm_shift_puncturedLattice_apply]
    by_cases hm : m=n
    · simp only [sourceAngularBetaSeriesTerm,if_pos hm,norm_zero,mul_zero,le_refl]
    rw [sourceAngularBetaSeriesTerm,if_neg hm]
    have hd := norm_sourceDirichletMidpointDisplacement_le_half_gap φ m
    rw [sourceDirichletMidpointDisplacement_apply] at hd
    have hg : ‖sourcePeriodicGapDisplacement (by simp) (by norm_num) φ.val m‖ ≤ ‖G m‖/(1+|(m:ℝ)|) :=
      (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using hG m)
    calc
      _ ≤ C*(‖sourcePeriodicGapDisplacement (by simp) (by norm_num) φ.val m‖+
          ‖canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet φ.val m-
            sourceStandardRootMidpoint (by simp) (by norm_num) φ.val m‖)/|((n-m:ℤ):ℝ)| := hbeta n m hm
      _ ≤ C*((3/2:ℝ)*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) φ.val m‖)/|((n-m:ℤ):ℝ)| :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hC) (abs_nonneg _)
      _ ≤ C*((3/2:ℝ)*(‖G m‖/(1+|(m:ℝ)|)))/|((n-m:ℤ):ℝ)| := by gcongr
      _ = _ := by rw [if_neg hm,Int.cast_sub,abs_sub_comm]; push_cast; ring
  obtain ⟨hs,hb⟩ := Coeff.summable_norm_reciprocal_of_weighted_hilbert G _ n ((3/2:ℝ)*C) (by positivity) hu
  have hnorm : ‖sourceAngularBetaCorrection (by simp) (by norm_num) n s φ.val‖ ≤
      ∑' m, ‖sourceAngularBetaSeriesTerm (by simp) (by norm_num) n s φ.val m‖ :=
    norm_tsum_le_tsum_norm hs
  exact (mul_le_mul_of_nonneg_left hnorm (by positivity)).trans (hb.trans_eq (by ring))

/-- The actual H1 gap sequence, with its original even-frequency weight. -/
def sourceH1WeightedGapSequence (a : ScalarDomain 2 × ScalarDomain 2) : Coeff 2 :=
  sourceWeightedGapSequence (by simp) (by norm_num) (SpectralWeight.sobolev 1 (by norm_num))
    sobolevSourceInclusion sobolevSourceWeightedPeriodOne weightedBaseToPair_sobolevSourceWeightedPeriodOne a

/-- The actual weighted gap sequence controls the inhomogeneous index bracket, including zero. -/
theorem sourceH1WeightedGapSequence_majorant (a : ScalarDomain 2 × ScalarDomain 2) (m : ℤ) :
    (1+|(m:ℝ)|)*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (sobolevSourceInclusion a) m‖ ≤
      ‖sourceH1WeightedGapSequence a m‖ := by
  change _ ≤ ‖((SpectralWeight.sobolev 1 (by norm_num)) (2*m):ℂ)*
    sourcePeriodicGapDisplacement (by simp) (by norm_num) (sobolevSourceInclusion a) m‖
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ((SpectralWeight.sobolev 1 (by norm_num)).toWeight.positive _)]
  norm_num only [SpectralWeight.sobolev_apply,Weight.sobolev_apply,Real.rpow_one,Int.cast_mul,Int.cast_ofNat,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  gcongr
  linarith [abs_nonneg (m:ℝ)]

namespace SourceAngularEtaLocalCommonDomainData
variable {W₀ B : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- On an H1 neighborhood of every real source, all actual beta corrections decay at rate 1/<n>. -/
theorem exists_local_uniform_betaCorrection_H1_decay
    (D : SourceAngularEtaLocalCommonDomainData (by simp) (by norm_num) W₀ B s)
    (a : realTypeSobolevSourceLocus) (ha : sobolevSourceInclusion a.val ∈ B) :
    ∃ U : Set (ScalarDomain 2 × ScalarDomain 2), IsOpen U ∧ a.val ∈ U ∧
      (∀ b ∈ U, sobolevSourceInclusion b ∈ B) ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ b : realTypeSobolevSourceLocus, b.val ∈ U → ∀ n : ℤ,
        (1+|(n:ℝ)|)*‖sourceAngularBetaCorrection (by simp) (by norm_num) n s (sobolevSourceInclusion b.val)‖ ≤ K := by
  obtain ⟨V,hV,haV,hVB,C,hC,hbeta⟩ := D.beta_bound (sobolevSourceInclusion a.val) ha
  obtain ⟨T,hT,haT,R,hR,hgap⟩ := exists_local_sourceWeightedGapSequence_bound (by simp) (by norm_num)
    (SpectralWeight.sobolev 1 (by norm_num)) sobolevSourceInclusion sobolevSourceWeightedPeriodOne
    weightedBaseToPair_sobolevSourceWeightedPeriodOne a.val
  refine ⟨sobolevSourceInclusion ⁻¹' V ∩ T,(hV.preimage sobolevSourceInclusion.continuous).inter hT,
    ⟨haV,haT⟩,(fun b hb => hVB hb.1),6*C*R,by positivity,?_⟩
  intro b hb n
  exact (sourceAngularBetaCorrection_weighted_bound s ⟨sobolevSourceInclusion b.val,b.property⟩
    (sourceH1WeightedGapSequence b.val) (sourceH1WeightedGapSequence_majorant b.val) C hC.le
    (hbeta _ hb.1) n).trans (mul_le_mul_of_nonneg_left (hgap _ hb.2) (by positivity))

end SourceAngularEtaLocalCommonDomainData
end NLS.ZakharovShabat
