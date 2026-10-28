import NLS.ZakharovShabat.SourcePQTopology
import NLS.ZakharovShabat.SourceLemma6_4
import NLS.SequenceSpaces.CompactPuncturedKernel

/-! # The literal reciprocal series and proof of Lemma 6.4

The actual complementary inverse has a weighted l1 representative with
unchanged original-domain coefficients. Its signed Fourier series uses the
literal nonresonant denominators. The shifted Holder display and the Young
p-power step retain the original norms, opposite shifts and exponent constants.
The finite conjugate moment formula requires p>1; the Holder map also covers p=1.
-/

noncomputable section
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual complementary inverse represented in the original weighted l1 pair. -/
def sourceLemma64Vector_original (hp : p ≠ ⊤) (w : SpectralWeight)
    (f : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    WeightedCoeffPair w.toWeight 1 :=
  (WeightedCoeffPair.toMax w.toWeight 1).symm
    (complementaryScalarL1 hp w.toWeight n z hz true f.fst,
     complementaryScalarL1 hp w.toWeight n z hz false f.snd)

/-- The l1 representative retains both original derivative-domain coefficients. -/
theorem sourceLemma64Vector_original_coefficients (hp : p ≠ ⊤) (w : SpectralWeight)
    (f : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) (k : ℤ) :
    let g := sourceWeightedDomainInput w (complementaryFreeDomainInverse w.toWeight n z hz f)
    (sourceLemma64Vector_original hp w f n z hz).fst.val k = g.fst.val k ∧
    (sourceLemma64Vector_original hp w f n z hz).snd.val k = g.snd.val k := by
  simp [sourceLemma64Vector_original,WeightedCoeffPair.toMax]

/-- The printed single Fourier series converges in the original weighted l1 pair norm. -/
theorem sourceLemma64Vector_original_hasSum (hp : p ≠ ⊤) (w : SpectralWeight)
    (f : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    HasSum (fun k : ℤ => if k = n then 0 else
      resonantSynthesis (p := 1) w.toWeight k
        ![f.fst.val (-k)/(z-(Real.pi:ℂ)*k),f.snd.val k/(z-(Real.pi:ℂ)*k)])
      (sourceLemma64Vector_original hp w f n z hz) := by
  convert sourceSignedFourierModes_hasSum (by simp) w.toWeight (sourceLemma64Vector_original hp w f n z hz) using 1
  funext k
  by_cases hk : k = n
  · simp [sourceLemma64Vector_original,WeightedCoeffPair.toMax,hk,
      show (![0,0] : Fin 2 → ℂ) = 0 by ext i; fin_cases i <;> rfl]
  · simp [sourceLemma64Vector_original,WeightedCoeffPair.toMax,complementarySymbol,hk,div_eq_mul_inv,mul_comm]

/-- The weighted Holder bound before replacing the reciprocal lattice norm by c_p. -/
theorem sourceLemma64Proof_norm_holder (hp : p ≠ ⊤) (w : Weight) (n : ℤ) (z : ℂ)
    (hz : z ∈ resonantStrip n) (b : Bool) (a : WeightedCoeff w p) :
    ‖complementaryScalarL1 hp w n z hz b a‖ ≤
      ‖Coeff.puncturedLattice p.conjExponent
        ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)‖*‖a‖ := by
  let : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  let hq := (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
  change ‖(WeightedCoeff.weightIsometry w 1).symm
    (Coeff.holderProduct (q := 1) (WeightedCoeff.weightIsometry w p a)
      (complementaryReciprocal hq n z hz b))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  calc
    _ ≤ ‖WeightedCoeff.weightIsometry w p a‖*‖complementaryReciprocal hq n z hz b‖ :=
      Coeff.norm_holderProduct_le _ _
    _ ≤ ‖a‖*‖Coeff.puncturedLattice p.conjExponent hq‖ := by
      rw [LinearIsometryEquiv.norm_map]
      exact mul_le_mul_of_nonneg_left (norm_complementaryReciprocal_le hq n z hz b) (norm_nonneg _)
    _ = _ := mul_comm _ _

/-- Exact weighted absolute reciprocal sum in each physical component and shift. -/
theorem sourceLemma64Proof_shifted_sum (hp : p ≠ ⊤) (w : SpectralWeight) (i n : ℤ) (z : ℂ)
    (hz : z ∈ resonantStrip n) (b : Bool) (a : WeightedCoeff w.toWeight p) :
    w.shiftedNorm i (complementaryScalarL1 hp w.toWeight n z hz b a) =
      ∑' k : ℤ, if freeFrequency b k = n then 0 else
        w (k+i)*‖a.val k‖/‖z-(Real.pi:ℂ)*(freeFrequency b k)‖ := by
  have h := w.shiftedNorm_rpow_eq_tsum (by simp : (1:ℝ≥0∞) ≠ ⊤) i
    (complementaryScalarL1 hp w.toWeight n z hz b a)
  simpa only [ENNReal.toReal_one,Real.rpow_one] using h.trans (by
    apply tsum_congr
    intro k
    by_cases hk : freeFrequency b k = n <;>
      simp [complementaryScalarL1_apply,complementarySymbol,hk,div_eq_mul_inv,mul_comm,mul_assoc])

/-- The exact reciprocal sum is controlled by the exponent-only lattice norm. -/
theorem sourceLemma64Proof_shifted_holder (hp : p ≠ ⊤) (w : SpectralWeight) (i n : ℤ) (z : ℂ)
    (hz : z ∈ resonantStrip n) (b : Bool) (a : WeightedCoeff w.toWeight p) :
    w.shiftedNorm i (complementaryScalarL1 hp w.toWeight n z hz b a) ≤
      ‖Coeff.puncturedLattice p.conjExponent
        ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)‖ *
        w.shiftedNorm i a := by
  rw [SpectralWeight.shiftedNorm,toShift_complementaryScalarL1]
  exact sourceLemma64Proof_norm_holder hp _ n z hz b (w.toShift i a)

/-- The printed Young step uses the same full pair norm and opposite component shifts. -/
theorem sourceLemma64Proof_young_power (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ f : WeightedCoeffPair w.toWeight p) (i n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    w.shiftedPairNorm i (weightedPotentialInverse hp w φ n z hz f)^p.toReal ≤
      ‖φ‖^p.toReal * (w.shiftedNorm (-i) (sourceLemma64Vector_original hp w f n z hz).snd^p.toReal +
        w.shiftedNorm i (sourceLemma64Vector_original hp w f n z hz).fst^p.toReal) := by
  have hp0 : 0 ≤ p.toReal := ENNReal.toReal_nonneg
  rw [w.shiftedPairNorm_rpow hp,weightedPotentialInverse_fst,weightedPotentialInverse_snd]
  have h₁ := (w.shiftedNorm_convolution_le (-i) φ.fst
    (complementaryScalarL1 hp w.toWeight n z hz false f.snd)).trans
      (mul_le_mul_of_nonneg_right (WithLp.norm_fst_le _ φ) (norm_nonneg _))
  have h₂ := (w.shiftedNorm_convolution_le i φ.snd
    (complementaryScalarL1 hp w.toWeight n z hz true f.fst)).trans
      (mul_le_mul_of_nonneg_right (WithLp.norm_snd_le _ φ) (norm_nonneg _))
  have h := add_le_add (Real.rpow_le_rpow (norm_nonneg _) h₁ hp0)
    (Real.rpow_le_rpow (norm_nonneg _) h₂ hp0)
  simpa [sourceLemma64Vector_original,WeightedCoeffPair.toMax,SpectralWeight.shiftedNorm,Real.mul_rpow (norm_nonneg _) (norm_nonneg _),mul_add] using h

/-- The conjugate lattice norm is the literal punctured power sum at p>1. -/
theorem sourceLemma64Proof_lattice_norm (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    ‖Coeff.puncturedLattice p.conjExponent
        ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)‖ =
      (∑' m : ℤ, if m = n then 0 else
        |((n-m : ℤ):ℝ)|^(-p.conjExponent.toReal))^(1/p.conjExponent.toReal) := by
  let : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  have hq : p.conjExponent ≠ ⊤ := ne_of_lt
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1)
  have hqpos : 0 < p.conjExponent.toReal := ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top))) hq
  let hq1 := (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
  rw [← Coeff.norm_shift n (Coeff.puncturedLattice p.conjExponent hq1),lp.norm_eq_tsum_rpow hqpos]
  congr 1
  apply tsum_congr
  intro m
  rw [Coeff.norm_shift_puncturedLattice_apply]
  by_cases hm : m = n
  · simp [hm,hqpos.ne']
  · simp [hm,abs_sub_comm,Real.rpow_neg,Real.inv_rpow]

/-- The exact scalar Holder display with the source punctured moment. -/
theorem sourceLemma64Proof_holder_display (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (i n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) (b : Bool) (a : WeightedCoeff w.toWeight p) :
    (∑' k : ℤ, if freeFrequency b k = n then 0 else
      w (k+i)*‖a.val k‖/‖z-(Real.pi:ℂ)*(freeFrequency b k)‖) ≤
      (∑' m : ℤ, if m = n then 0 else
        |((n-m : ℤ):ℝ)|^(-p.conjExponent.toReal))^(1/p.conjExponent.toReal) * w.shiftedNorm i a := by
  rw [← sourceLemma64Proof_shifted_sum hp w i n z hz b a,← sourceLemma64Proof_lattice_norm hp hp1 n]
  exact sourceLemma64Proof_shifted_holder hp w i n z hz b a

/-- The two Holder bounds recombine with the exact original opposite-shift power. -/
theorem sourceLemma64Proof_holder_power (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ f : WeightedCoeffPair w.toWeight p) (i n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    ‖φ‖^p.toReal * (w.shiftedNorm (-i) (sourceLemma64Vector_original hp w f n z hz).snd^p.toReal +
        w.shiftedNorm i (sourceLemma64Vector_original hp w f n z hz).fst^p.toReal) ≤
      (Coeff.complementaryConstant p hp)^p.toReal * ‖φ‖^p.toReal *
        w.shiftedPairNorm (-i) f^p.toReal := by
  let C := Coeff.complementaryConstant p hp
  have hC : 0 ≤ C := Coeff.complementaryConstant_nonneg p hp
  have hs : 0 ≤ w.shiftedNorm (-i) f.snd := norm_nonneg _
  have hf : 0 ≤ w.shiftedNorm i f.fst := norm_nonneg _
  have h₁ := shiftedNorm_complementaryScalarL1_le hp w (-i) n z hz false f.snd
  have h₂ := shiftedNorm_complementaryScalarL1_le hp w i n z hz true f.fst
  change ‖φ‖^p.toReal *
    (w.shiftedNorm (-i) (complementaryScalarL1 hp w.toWeight n z hz false f.snd)^p.toReal +
      w.shiftedNorm i (complementaryScalarL1 hp w.toWeight n z hz true f.fst)^p.toReal) ≤ _
  calc
    _ ≤ ‖φ‖^p.toReal * ((C*w.shiftedNorm (-i) f.snd)^p.toReal +
      (C*w.shiftedNorm i f.fst)^p.toReal) := by
      gcongr <;> exact norm_nonneg _
    _ = _ := by
      rw [w.shiftedPairNorm_rpow hp,neg_neg,Real.mul_rpow hC hs,Real.mul_rpow hC hf]
      ring

end NLS.ZakharovShabat
