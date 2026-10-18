import NLS.ZakharovShabat.SourceMidpointProductSobolevDecay
import NLS.ZakharovShabat.SourceSquaredGapSobolevDecay
import NLS.ZakharovShabat.SourceCriticalOffsetSobolevMajorant
import NLS.ZakharovShabat.SourceSingleRootGapCorrectionLimit
import NLS.ZakharovShabat.SourceSingleRootQuotientAsymptoticDiscSup
import NLS.ZakharovShabat.SourceCriticalRootRatioCollapsed

/-! # Complex Sobolev normalization-factor decay

The actual complementary normalization factor approaches its free value at inverse-bracket rate on distant refined resonant discs, uniformly on one complex source neighborhood.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The actual complementary normalization factor has inverse-bracket decay on complex Sobolev neighborhoods. -/
theorem exists_local_normalizedSobolevCriticalFactor_decay (φ : realTypeSourceLocus 2) :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ φ.val ∈ U ∧
      ∃ N : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs →
        ∀ z ∈ refinedResonantDisk n,
          (1+|(n:ℝ)|)*‖I*sourceCriticalRootRatioExtension (by simp) (by norm_num) n
            (normalizedWeightedSource (SpectralWeight.sobolev 1 (by norm_num)) ψ) z-1‖ ≤ K := by
  let w := SpectralWeight.sobolev 1 (by norm_num)
  let φu : realTypeSourceSubmodule 2 :=
    ⟨normalizedWeightedSource w φ.val,normalizedWeightedSource_realType w φ.val φ.property⟩
  obtain ⟨Va,hVa,hφa,M,hM,ha⟩ := exists_local_normalizedSobolevCriticalOffset_majorants φ
  obtain ⟨N₀,ε,_,_,Vd,hVd,_,hφd,C,R,H,hC,_,_,N,hN,hdata⟩ :=
    exists_local_sourceSingleRootQuotientAsymptotic_data (by simp) (by norm_num) φu.val φu.property
  let U := Va ∩ normalizedWeightedSource w ⁻¹' Vd
  have hU : IsOpen U := hVa.inter (hVd.preimage (continuous_normalizedWeightedSource w))
  let P := ‖Coeff.puncturedLattice (2:ℝ≥0∞).conjExponent
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt (2:ℝ≥0∞) (2:ℝ≥0∞).conjExponent).mp (by norm_num))‖
  have hP : 0 ≤ P := by
    dsimp only [P]
    exact lp.norm_nonneg' _
  have hC0 : 0 ≤ C := by linarith
  let K := Real.exp (C*M*P)*C^2*(4*M^2)+(4*C*M)*Real.exp (4*C*M)
  refine ⟨U,hU,⟨hφa,hφd⟩,N,K,by dsimp only [K]; positivity,?_⟩
  intro ψ hψ n hn z hz
  let χ := normalizedWeightedSource w ψ
  obtain ⟨G,A,hG,hA,hnG,hnA,hcrit⟩ := ha ψ hψ.1
  let α := sourceCriticalMidpointOffsetAtExponent (by simp) (by norm_num) (q := 2) (by norm_num) χ
  let a := canonicalCriticalDisplacement (by simp) (by norm_num) (periodOnePotential χ) (periodOnePotential_mem χ)
  have hα (m : ℤ) : displacedRoots a m-canonicalPeriodicMidpoint (by simp) (by norm_num)
      (periodOnePotential χ) (periodOnePotential_mem χ) m = α m := by
    have he : displacedRoots a m = canonicalCriticalPoints (by simp) (by norm_num)
        (periodOnePotential χ) (periodOnePotential_mem χ) m := by
      simp only [a,displacedRoots,canonicalCriticalDisplacement_apply]
      ring
    rw [he]
    exact hcrit m
  have hαnorm : ‖α‖ ≤ M := by
    apply le_trans _ hnA
    apply lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0)
    intro m
    have h := hA m
    change (1+|(m:ℝ)|)*‖α m‖ ≤ ‖A m‖ at h
    nlinarith [abs_nonneg (m:ℝ),norm_nonneg (α m)]
  obtain ⟨_,_,hsep,hsmall,hdom⟩ := hdata χ hψ.2
  have hziso : z ∈ sourceIsolatingDisc (by simp) (by norm_num) φu.val N₀ ε n := by
    simpa only [sourceIsolatingDisc,if_neg (by omega : ¬n.natAbs ≤ N₀)] using hz
  have hmid := norm_sourceMidpointProductRow_weighted_bound (by simp) (by norm_num) χ α A hA n z C hC
    (fun m hm => hsep n m (Ne.symm hm) z hziso)
  have hmid' : (1+|(n:ℝ)|)*‖sourceMidpointProductRow (by simp) (by norm_num) χ α n z‖ ≤
      (4*C*M)*Real.exp (4*C*M) := hmid.trans (by gcongr)
  let row := ∑' m, sourceSquaredGapReciprocalTerm (by simp) (by norm_num) χ n m
  have hrow0 : 0 ≤ row := tsum_nonneg (fun m => by
    unfold sourceSquaredGapReciprocalTerm
    split_ifs <;> positivity)
  have hrow2 : (1+|(n:ℝ)|)^2*row ≤ 4*M^2 :=
    (sourceSquaredGapReciprocalRow_weighted_bound (by simp) (by norm_num) χ G hG n).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg G) hnG 2) (by norm_num))
  have hrow : (1+|(n:ℝ)|)*row ≤ 4*M^2 :=
    (mul_le_mul_of_nonneg_right (by nlinarith [abs_nonneg (n:ℝ)] : 1+|(n:ℝ)| ≤ (1+|(n:ℝ)|)^2) hrow0).trans hrow2
  have hcor := norm_sourceSingleRootQuotientJointProduct_sub_midpoint_le_of_small_row
    (by simp) (by norm_num) (by norm_num : (2:ℝ≥0∞) ≠ ⊤)
    φu.val χ a α hα N₀ ε C hC hsep n z hziso (hdom a n hn z hziso) (hsmall n hn)
  have hcor' : ‖sourceSingleRootQuotientJointProduct (by simp) (by norm_num) n (z,(a,χ))-
      (sourceMidpointProductRow (by simp) (by norm_num) χ α n z+1)‖ ≤ Real.exp (C*M*P)*C^2*row := by
    apply hcor.trans
    change Real.exp (C*‖α‖*P)*C^2*row ≤ _
    gcongr
  have hfactor : I*sourceCriticalRootRatioExtension (by simp) (by norm_num) n χ z =
      sourceSingleRootQuotientJointProduct (by simp) (by norm_num) n (z,(a,χ)) := by
    change I*(-I*sourceSingleRootQuotientJointProduct (by simp) (by norm_num) n (z,(a,χ))) = _
    rw [← mul_assoc]
    simp
  rw [hfactor]
  let Q := sourceSingleRootQuotientJointProduct (by simp) (by norm_num) n (z,(a,χ))
  let T := sourceMidpointProductRow (by simp) (by norm_num) χ α n z
  have hsplit : Q-1 = (Q-(T+1))+T := by ring
  change (1+|(n:ℝ)|)*‖Q-1‖ ≤ K
  rw [hsplit]
  calc
    _ ≤ (1+|(n:ℝ)|)*(‖Q-(T+1)‖+‖T‖) := mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ ≤ (1+|(n:ℝ)|)*(Real.exp (C*M*P)*C^2*row+‖T‖) :=
      mul_le_mul_of_nonneg_left (add_le_add hcor' (le_refl ‖T‖)) (by positivity)
    _ = (Real.exp (C*M*P)*C^2)*((1+|(n:ℝ)|)*row)+(1+|(n:ℝ)|)*‖T‖ := by ring
    _ ≤ (Real.exp (C*M*P)*C^2)*(4*M^2)+(4*C*M)*Real.exp (4*C*M) :=
      add_le_add (mul_le_mul_of_nonneg_left hrow (by positivity)) hmid'
    _ = K := rfl

end NLS.ZakharovShabat
