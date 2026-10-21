import NLS.ZakharovShabat.SourceBirkhoffInverseFourierAnalytic
import NLS.ZakharovShabat.SourceBirkhoffSobolevEstimates

/-! # Uniform forward and inverse Fourier one-smoothing

Physical norm comparison and the two-sided Sobolev estimates bound inverse sources on native target balls. One constructed family has bounded analytic one-derivative remainders in both directions.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The native maximum Sobolev norm is bounded by the exact physical
component-sum Sobolev norm. -/
theorem norm_native_le_sourcePiSobolevCoordinates (m : ℕ) (a : SobolevSource m) :
    ‖a‖ ≤ ‖sourcePiSobolevCoordinates m m le_rfl a‖ := by
  have hs (c : ScalarSobolev m) : ‖c‖ ≤ ‖sourcePiSobolevScalar m m le_rfl c‖ := by
    rw [WeightedCoeff.norm_eq]
    apply lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0)
    intro n
    simp only [WeightedCoeff.weightEquiv_apply,sourcePiSobolevScalar_apply,norm_mul,
      Complex.norm_real,Real.norm_eq_abs]
    rw [abs_of_pos ((Weight.sobolev m).positive n),
      abs_of_pos ((SpectralWeight.piSobolev m (Nat.cast_nonneg m)).positive (2*n))]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    simp only [Weight.sobolev_apply,SpectralWeight.piSobolev_apply,Real.rpow_natCast,
      Int.cast_mul,Int.cast_ofNat,abs_mul,abs_of_pos Real.pi_pos,abs_of_pos (by norm_num : (0:ℝ)<2)]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [abs_nonneg (n:ℝ),Real.pi_gt_three]
  change max ‖a.1‖ ‖a.2‖ ≤ _
  exact max_le ((hs a.1).trans ((norm_fst_le (CoeffPair.toMax 2 (sourcePiSobolevCoordinates m m le_rfl a))).trans (CoeffPair.norm_toMax_le _)))
    ((hs a.2).trans ((norm_snd_le (CoeffPair.toMax 2 (sourcePiSobolevCoordinates m m le_rfl a))).trans (CoeffPair.norm_toMax_le _)))

/-- Comparing the physical Fourier weight to the original period-one
Sobolev weight, uniformly at every lower integer order. -/
theorem sourcePiWeight_le_native (m k : ℕ) (hk : k ≤ m) (n : ℤ) :
    (1+|((2*n:ℤ):ℝ)*Real.pi|)^k ≤ (2*Real.pi)^m * Weight.sobolev m n := by
  have h₁ : 1 ≤ 2*Real.pi := by linarith [Real.pi_gt_three]
  calc
    _ ≤ (1+|((2*n:ℤ):ℝ)*Real.pi|)^m :=
      pow_le_pow_right₀ (by linarith [abs_nonneg (((2*n:ℤ):ℝ)*Real.pi)]) hk
    _ ≤ ((2*Real.pi)*(1+|(n:ℝ)|))^m := by
      apply pow_le_pow_left₀ (by positivity)
      simp only [Int.cast_mul,Int.cast_ofNat,abs_mul,abs_of_pos Real.pi_pos,
        abs_of_pos (by norm_num : (0:ℝ)<2)]
      nlinarith [abs_nonneg (n:ℝ)]
    _ = _ := by rw [mul_pow,Weight.sobolev_apply,Real.rpow_natCast]

/-- A physical real coefficient sequence is bounded by its native
Sobolev realization, with an explicit constant independent of the sequence. -/
theorem norm_real_physical_coeff_le_native (m k : ℕ) (hk : k ≤ m)
    (q : RealCoeff 2)
    (z : WeightedRealCoeff (sourceFrequencyWeight (sourceSobolevSpectralWeight m (Nat.cast_nonneg m))) 2)
    (h : ∀ n : ℤ, (q n:ℂ) = ((1+|((2*n:ℤ):ℝ)*Real.pi|)^k:ℝ)*z.val.val n) :
    ‖q‖ ≤ (2*Real.pi)^m*‖z‖ := by
  have hc : ‖RealCoeff.complexCLM 2 q‖ = ‖q‖ := by
    apply le_antisymm <;> apply lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0) <;> intro n <;> simp
  rw [← hc]
  calc
    _ ≤ ‖(((2*Real.pi)^m:ℝ):ℂ) • WeightedCoeff.weightEquiv _ 2 z.val‖ := by
      apply lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0)
      intro n
      change ‖(q n:ℂ)‖ ≤ _
      rw [h n]
      simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,WeightedCoeff.weightEquiv_apply,
        norm_mul,Complex.norm_real,Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity : 0 ≤ (1+|((2*n:ℤ):ℝ)*Real.pi|)^k),
        abs_of_nonneg (by positivity : 0 ≤ (2*Real.pi)^m),
        abs_of_pos ((sourceFrequencyWeight (sourceSobolevSpectralWeight m (Nat.cast_nonneg m))).positive n)]
      rw [show (sourceFrequencyWeight (sourceSobolevSpectralWeight m (Nat.cast_nonneg m))).value n =
        Weight.sobolev m n from sourceSobolevSpectralWeight_even m (Nat.cast_nonneg m) n,← mul_assoc]
      exact mul_le_mul_of_nonneg_right (sourcePiWeight_le_native m k hk n) (norm_nonneg _)
    _ = _ := by
      rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      rfl

namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
variable (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
include D

/-- All lower physical Birkhoff norms of an inverse source are bounded
by the actual native target norm. -/
theorem sobolevCoordinates_nativeInverse_norm_le (m : ℕ) (hm : 1 ≤ m)
    (k : ℕ) (hk : k ≤ m) (z : originalRealSobolevTarget m) :
    let a := (D.originalWeightedRealSobolevEquiv (by norm_num) m (Nat.cast_nonneg m)).symm z
    ‖D.sobolevCoordinates m hm k hk
      ⟨originalRealSobolevToHigher m a,originalRealSobolevToHigher_real m a⟩‖ ≤
      2*(2*Real.pi)^m*‖z‖ := by
  let a := (D.originalWeightedRealSobolevEquiv (by norm_num) m (Nat.cast_nonneg m)).symm z
  let b : realTypeHigherSobolevSourceLocus m :=
    ⟨originalRealSobolevToHigher m a,originalRealSobolevToHigher_real m a⟩
  let q := D.sobolevCoordinates m hm k hk b
  let C := (2*Real.pi)^m
  change ‖q‖ ≤ 2*C*‖z‖
  have hφ : higherSobolevSourceInclusion m b.val = (originalWeightedRealSource _ a).val := by
    change higherSobolevSourceInclusion m (originalSobolevToHigher m a.val) = _
    rw [higherSobolevSourceInclusion_originalSobolevToHigher,originalWeightedSourceCLM_real]
  have hx : ‖q.fst‖ ≤ C*‖z.fst‖ := by
    apply norm_real_physical_coeff_le_native m k hk q.fst z.fst
    intro n
    have he := congrArg (fun v : Coeff 2 × Coeff 2 => v.1 n)
      (D.real_map_complex_inclusion ⟨higherSobolevSourceInclusion m b.val,b.property⟩)
    change ((sourceRealBirkhoffMap (by simp) (by norm_num) s
      ⟨higherSobolevSourceInclusion m b.val,b.property⟩).1 n:ℂ) =
      (sourceBirkhoffMap (by simp) (by norm_num) s (higherSobolevSourceInclusion m b.val)).1 n at he
    change (((1+|((2*n:ℤ):ℝ)*Real.pi|)^k*
      (sourceRealBirkhoffMap (by simp) (by norm_num) s
        ⟨higherSobolevSourceInclusion m b.val,b.property⟩).1 n:ℝ):ℂ) = _
    rw [Complex.ofReal_mul,he,hφ,(D.birkhoffMap_nativeSobolevInverse_coordinates m z n).1]
  have hy : ‖q.snd‖ ≤ C*‖z.snd‖ := by
    apply norm_real_physical_coeff_le_native m k hk q.snd z.snd
    intro n
    have he := congrArg (fun v : Coeff 2 × Coeff 2 => v.2 n)
      (D.real_map_complex_inclusion ⟨higherSobolevSourceInclusion m b.val,b.property⟩)
    change ((sourceRealBirkhoffMap (by simp) (by norm_num) s
      ⟨higherSobolevSourceInclusion m b.val,b.property⟩).2 n:ℂ) =
      (sourceBirkhoffMap (by simp) (by norm_num) s (higherSobolevSourceInclusion m b.val)).2 n at he
    change (((1+|((2*n:ℤ):ℝ)*Real.pi|)^k*
      (sourceRealBirkhoffMap (by simp) (by norm_num) s
        ⟨higherSobolevSourceInclusion m b.val,b.property⟩).2 n:ℝ):ℂ) = _
    rw [Complex.ofReal_mul,he,hφ,(D.birkhoffMap_nativeSobolevInverse_coordinates m z n).2]
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hzx : ‖z.fst‖ ≤ ‖z‖ :=
    (norm_fst_le z.ofLp).trans (norm_ofLp_prod_le z)
  have hzy : ‖z.snd‖ ≤ ‖z‖ :=
    (norm_snd_le z.ofLp).trans (norm_ofLp_prod_le z)
  have h1 := hx.trans (mul_le_mul_of_nonneg_left hzx hC)
  have h2 := hy.trans (mul_le_mul_of_nonneg_left hzy hC)
  have hq := norm_withLp_prod_rpow (p := 2) (by simp) q
  norm_num only [ENNReal.toReal_ofNat,Real.rpow_two] at hq
  have h1sq := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h2sq := pow_le_pow_left₀ (norm_nonneg _) h2 2
  nlinarith [norm_nonneg q,mul_nonneg hC (norm_nonneg z),sq_nonneg (C*‖z‖)]

/-- The actual Sobolev inverse takes every bounded native target ball
to a bounded original higher Sobolev source ball. -/
theorem nativeSobolevInverse_uniform_higher_ball (m : ℕ) (hm : 1 ≤ m)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : originalRealSobolevTarget m, ‖z‖ ≤ R →
      ‖originalRealSobolevToHigher m
        ((D.originalWeightedRealSobolevEquiv (by norm_num) m (Nat.cast_nonneg m)).symm z)‖ ≤ K := by
  obtain ⟨_,d,_,hd,hbounds⟩ := D.exists_sobolev_two_sided_bounds m hm
  let C := 2*(2*Real.pi)^m
  refine ⟨d*(C*R+(1+C*R)^(4*m-3)*(C*R)),by dsimp [C]; positivity,?_⟩
  intro z hz
  let a := (D.originalWeightedRealSobolevEquiv (by norm_num) m (Nat.cast_nonneg m)).symm z
  let b : realTypeHigherSobolevSourceLocus m :=
    ⟨originalRealSobolevToHigher m a,originalRealSobolevToHigher_real m a⟩
  have hq (k : ℕ) (hk : k ≤ m) : ‖D.sobolevCoordinates m hm k hk b‖ ≤ C*R :=
    (D.sobolevCoordinates_nativeInverse_norm_le m hm k hk z).trans
      (mul_le_mul_of_nonneg_left hz (by positivity))
  apply (norm_native_le_sourcePiSobolevCoordinates m b.val).trans
  apply (hbounds b).2.trans
  gcongr
  · exact hq m le_rfl
  · exact hq 1 hm
  · exact hq 0 (Nat.zero_le m)

/-- The stronger inverse Fourier remainder is uniformly bounded on
every native real Sobolev target ball, for each positive integer order. -/
theorem inverseSobolevFourierRemainder_uniform_ball (m : ℕ) (hm : 1 ≤ m)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : originalRealSobolevTarget m, ‖z‖ ≤ R →
      ‖D.inverseSobolevFourierRemainder m z‖ ≤ C := by
  obtain ⟨K,hK,hInv⟩ := D.nativeSobolevInverse_uniform_higher_ball m hm R hR
  obtain ⟨M,hM,hE⟩ := D.higherSobolevBirkhoffFourierRemainder_uniform_real_ball m hm K hK
  let L := sourceSobolevBirkhoffFourierInverse ((m:ℝ)+1)
  refine ⟨‖L‖*M,mul_nonneg (norm_nonneg L) hM,?_⟩
  intro z hz
  let a := (D.originalWeightedRealSobolevEquiv (by norm_num) m (Nat.cast_nonneg m)).symm z
  let b : realTypeHigherSobolevSourceLocus m :=
    ⟨originalRealSobolevToHigher m a,originalRealSobolevToHigher_real m a⟩
  change ‖-(L (higherSobolevBirkhoffFourierRemainder m s b.val))‖ ≤ _
  rw [norm_neg]
  exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hE b (hInv z hz)) (norm_nonneg L))

/-- The actual inverse Fourier remainder takes arbitrary bounded target
sets to bounded sets in the space gaining one derivative. -/
theorem inverseSobolevFourierRemainder_image_isBounded (m : ℕ) (hm : 1 ≤ m)
    {S : Set (originalRealSobolevTarget m)} (hS : Bornology.IsBounded S) :
    Bornology.IsBounded (D.inverseSobolevFourierRemainder m '' S) := by
  obtain ⟨R,hR⟩ := hS.exists_norm_le
  obtain ⟨C,_,hC⟩ := D.inverseSobolevFourierRemainder_uniform_ball m hm (max R 0) (le_max_right _ _)
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨C,?_⟩
  rintro _ ⟨z,hz,rfl⟩
  exact hC z ((hR z hz).trans (le_max_left _ _))

end SourceBirkhoffMapComplexData

/-- A single constructed Birkhoff family has analytic one-derivative
Fourier remainders in both directions, uniformly on every native real
Sobolev ball at every positive integer order. -/
theorem exists_sourceBirkhoffMap_bounded_forward_inverse_one_smoothing :
    ∃ W₀ B W : Set (CoeffPair 2), ∃ s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n,
      ∃ D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s,
      ∀ m : ℕ, 1 ≤ m →
        AnalyticOnNhd ℝ (fun a => higherSobolevBirkhoffFourierRemainder m s
          (originalRealSobolevToHigher m a)) univ ∧
        AnalyticOnNhd ℝ (D.inverseSobolevFourierRemainder m) univ ∧
        (∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, 0 ≤ C ∧
          ∀ a : weightedRealSourceSubmodule (p := 2)
            (sourceSobolevSpectralWeight m (Nat.cast_nonneg m)), ‖a‖ ≤ R →
            ‖higherSobolevBirkhoffFourierRemainder m s (originalRealSobolevToHigher m a)‖ ≤ C) ∧
        (∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, 0 ≤ C ∧
          ∀ z : originalRealSobolevTarget m, ‖z‖ ≤ R → ‖D.inverseSobolevFourierRemainder m z‖ ≤ C) := by
  obtain ⟨W₀,B,W,s,D⟩ := exists_sourceBirkhoffMap_complex_analytic (p := 2) (by simp) (by norm_num)
  exact ⟨W₀,B,W,s,D,fun m hm =>
    ⟨D.higherSobolevBirkhoffFourierRemainder_originalReal_analytic m hm,
     D.inverseSobolevFourierRemainder_analytic m hm,
     D.higherSobolevBirkhoffFourierRemainder_originalReal_uniform_ball m hm,
     D.inverseSobolevFourierRemainder_uniform_ball m hm⟩⟩

end NLS.ZakharovShabat
