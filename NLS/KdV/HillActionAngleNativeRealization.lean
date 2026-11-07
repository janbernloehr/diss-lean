import NLS.KdV.HillActionAngleEnergyDomain
import NLS.KdV.HillAbelianWeightNormBound
import NLS.SequenceSpaces.PositiveWeightedDomination
import NLS.SequenceSpaces.PositiveHalfWeightBound

/-! Actual weighted minus-half Cartesian sequence realizations, with
ONE local norm bound near EVERY real native H-minus-one source. The
full-l2 ACTUAL frequency gap and AUX displacement supply the majorant.
The target uses the literal positive-index Sobolev weight, not only scalar bounds. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat NLS.LpSequence
open scoped ENNReal Classical
namespace NLS.KdV

theorem exists_local_uniform_actionAngle_native_realizations (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧ U ⊆ hillHminusActionAngleEnergyDomain ∧
      ∃ M : ℝ, 0 < M ∧ ∀ a ∈ U,
        (∃ x : WeightedCoeff (Weight.positiveSobolev (-1/2)) 2,
          (∀ k, x.val k = positiveScalarExtension (fun n => hillHminusActionAngleX n a) k) ∧ ‖x‖ ≤ M) ∧
        (∃ y : WeightedCoeff (Weight.positiveSobolev (-1/2)) 2,
          (∀ k, y.val k = positiveScalarExtension (fun n => hillHminusActionAngleY n a) k) ∧ ‖y‖ ≤ M) := by
  obtain ⟨A,H⟩ := exists_miuraHillPsiFamily_with_original_estimates
  obtain ⟨P,hq,_,hPA⟩ := exists_hillProductEquationPatch_with_family A q hr
  have HP : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots := by rw [hPA]; exact H
  obtain ⟨Ua,hUa,hqa,_,Ca,hCa,hamp⟩ := exists_local_uniform_actionAngle_diagonal_bound q
    (real_mem_hillHminusActionAmplitudeDomain q hr)
  obtain ⟨Uf,hUf,hqf,_,Cf,hCf,hfreq⟩ := P.exists_local_uniform_physicalOnIndexCartesian_frequency_bound HP q
    (P.real_mem_physicalDirichletSource q hq hr)
  obtain ⟨rd,hrd,_,heq⟩ := exists_common_intrinsic_diagonal_Cartesian_patch_ball P q hq hr
  obtain ⟨rB,B,hrB,hB,hupper⟩ := P.exists_uniform_source_frequency_midpoint_index_upper_bound q hq hr
  obtain ⟨Uw,hUw,hqw,_,R,hR,hweight⟩ := P.exists_local_abelianWeight_norm_bound q hq
  let U := (((Ua ∩ Uf) ∩ ball q rd) ∩ (ball q rB ∩ Uw)) ∩ hillHminusActionAngleEnergyDomain
  let C := Ca*Cf
  let Q := C*B
  have hC : 0 < C := mul_pos hCa hCf
  have hQ : 0 ≤ Q := mul_nonneg hC.le hB
  refine ⟨U,(((hUa.inter hUf).inter isOpen_ball).inter (isOpen_ball.inter hUw)).inter
    isOpen_hillHminusActionAngleEnergyDomain,
    ⟨⟨⟨⟨hqa,hqf⟩,mem_ball_self hrd⟩,mem_ball_self hrB,hqw⟩,real_mem_hillHminusActionAngleEnergyDomain q hr⟩,
    (fun _ h => h.2),Q*R+1,by positivity,?_⟩
  intro a ha
  let g := sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi a)
  let d := P.physicalAbelianMidpointDisplacement a
  have hseq (n : ℕ+) :
      ‖(Weight.positiveSobolev (-1/2) ((n:ℕ):ℤ):ℂ)*hillHminusActionAngleX n a‖ ≤
        Q*(‖g ((n:ℕ):ℤ)‖+‖d ((n:ℕ):ℤ)‖) ∧
      ‖(Weight.positiveSobolev (-1/2) ((n:ℕ):ℤ):ℂ)*hillHminusActionAngleY n a‖ ≤
        Q*(‖g ((n:ℕ):ℤ)‖+‖d ((n:ℕ):ℤ)‖) := by
    let τ := sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi a) ((n:ℕ):ℤ)
    let W := ‖g ((n:ℕ):ℤ)‖+‖d ((n:ℕ):ℤ)‖
    have hW : 0 ≤ W := add_nonneg (norm_nonneg _) (norm_nonneg _)
    have hf := hfreq a ha.1.1.1.2 n
    rw [← P.physicalAbelianMidpointDisplacement_apply] at hf
    have ham := hamp a ha.1.1.1.1 n
    have he := heq n a ha.1.1.2
    rw [he.1,he.2] at ham
    have hca : 0 ≤ Ca/Real.sqrt (n:ℕ) := div_nonneg hCa.le (Real.sqrt_nonneg _)
    have hp : ‖hillHminusActionAngleFactorPlus n a‖ ≤ (C/Real.sqrt (n:ℕ))*‖τ‖*W :=
      ham.1.trans (by
        have h := mul_le_mul_of_nonneg_left hf.1 hca
        convert h using 1; dsimp only [C,τ,W,g,d]; ring)
    have hm : ‖hillHminusActionAngleFactorMinus n a‖ ≤ (C/Real.sqrt (n:ℕ))*‖τ‖*W :=
      ham.2.trans (by
        have h := mul_le_mul_of_nonneg_left hf.2 hca
        convert h using 1; dsimp only [C,τ,W,g,d]; ring)
    have hxy := norm_hillHminusActionAngleXY_le_of_factor_bounds n a _ hp hm
    exact ⟨Weight.norm_positiveSobolev_neg_half_mul_le_of_frequency_bound n _ τ C B W hC.le hW hxy.1
        (hupper a ha.1.2.1 n),
      Weight.norm_positiveSobolev_neg_half_mul_le_of_frequency_bound n _ τ C B W hC.le hW hxy.2
        (hupper a ha.1.2.1 n)⟩
  obtain ⟨x,hx,hnx⟩ := WeightedCoeff.exists_positiveScalarExtension_of_weighted_norm_le
    (Weight.positiveSobolev (-1/2)) g d (fun n => hillHminusActionAngleX n a) Q hQ (fun n => (hseq n).1)
  obtain ⟨y,hy,hny⟩ := WeightedCoeff.exists_positiveScalarExtension_of_weighted_norm_le
    (Weight.positiveSobolev (-1/2)) g d (fun n => hillHminusActionAngleY n a) Q hQ (fun n => (hseq n).2)
  have hw := mul_le_mul_of_nonneg_left (hweight a ha.1.2.2) hQ
  exact ⟨⟨x,hx,hnx.trans (by dsimp only [g,d] at hnx; linarith)⟩,
    ⟨y,hy,hny.trans (by dsimp only [g,d] at hny; linarith)⟩⟩

end NLS.KdV
