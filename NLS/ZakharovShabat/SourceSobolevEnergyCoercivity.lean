import NLS.ZakharovShabat.SourceSobolevHamiltonianIdentification
import NLS.ZakharovShabat.SourceFiniteGapNLSVariation

/-! # Coercivity of the defocusing physical energy

The H¹ weight is controlled by the physical mass and kinetic energy.
On the real source locus the quartic term is nonnegative, so mass plus
physical Hamiltonian controls the first-component H¹ norm and its continuous synthesis.
-/
noncomputable section
open Set Complex MeasureTheory NLS.Fourier
open scoped ComplexConjugate ENNReal
namespace NLS.ZakharovShabat

private theorem hilbert_norm_sq (a : Coeff 2) : ‖a‖^2 = ∑' n : ℤ, ‖a n‖^2 := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
    lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) a

private theorem summable_hilbert_norm_sq (a : Coeff 2) : Summable (fun n : ℤ => ‖a n‖^2) := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
    (lp.memℓp a).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)

/-- The physical derivative and mass control the original scalar H¹ norm. -/
theorem norm_scalarSobolev_sq_le (a : ScalarDomain 2) :
    ‖a‖^2 ≤ 2*(‖scalarInclusion a‖^2 + ‖periodOneDerivative a‖^2) := by
  let w := WeightedCoeff.weightEquiv (Weight.sobolev 1) 2 a
  have hb (n : ℤ) : ‖w n‖^2 ≤ 2*(‖scalarInclusion a n‖^2 + ‖periodOneDerivative a n‖^2) := by
    have hd : |(n : ℝ)| *‖a.val n‖ ≤ ‖periodOneDerivative a n‖ := by
      rw [periodOneDerivative_apply]
      simp only [norm_mul,norm_ofNat,norm_I,norm_real,Real.norm_eq_abs,
        abs_of_pos Real.pi_pos,Complex.norm_intCast,mul_one]
      have hn : 0 ≤ |(n : ℝ)| *‖a.val n‖ := mul_nonneg (abs_nonneg _) (norm_nonneg _)
      have hp : 1 ≤ 2*Real.pi := by linarith [Real.pi_gt_three]
      have hb := mul_le_mul_of_nonneg_right hp hn
      simpa only [one_mul,mul_assoc,Int.cast_abs] using hb
    have hw : ‖w n‖ = (1+|(n : ℝ)|)*‖a.val n‖ := by
      simp only [w,WeightedCoeff.weightEquiv_apply,Weight.sobolev_apply,Real.rpow_one,
        norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ 1+|(n : ℝ)|)]
    rw [hw,scalarInclusion_apply]
    have hn := norm_nonneg (a.val n)
    have hk := norm_nonneg (periodOneDerivative a n)
    have ht : (1+|(n : ℝ)|)*‖a.val n‖ ≤ ‖a.val n‖+‖periodOneDerivative a n‖ := by nlinarith
    have hpos : 0 ≤ (1+|(n : ℝ)|)*‖a.val n‖ := by positivity
    nlinarith [sq_nonneg (‖a.val n‖-‖periodOneDerivative a n‖)]
  change ‖w‖^2 ≤ _
  rw [hilbert_norm_sq,hilbert_norm_sq (scalarInclusion a),hilbert_norm_sq (periodOneDerivative a)]
  calc
    _ ≤ ∑' n : ℤ, 2*(‖scalarInclusion a n‖^2+‖periodOneDerivative a n‖^2) :=
      (summable_hilbert_norm_sq w).tsum_le_tsum hb
        (((summable_hilbert_norm_sq (scalarInclusion a)).add
          (summable_hilbert_norm_sq (periodOneDerivative a))).mul_left 2)
    _ = _ := by
      rw [tsum_mul_left,(summable_hilbert_norm_sq (scalarInclusion a)).tsum_add
        (summable_hilbert_norm_sq (periodOneDerivative a))]

private theorem pairing_star_self (c : Coeff 2) :
    Coeff.dualPairing c (star c) = (‖c‖^2 : ℝ) := by
  calc
    _ = inner ℂ c c := by
      rw [Coeff.dualPairing_apply,lp.inner_eq_tsum]
      apply tsum_congr
      intro n
      simp only [lp.star_apply,RCLike.inner_apply',starRingEnd_apply,mul_comm]
    _ = _ := by rw [inner_self_eq_norm_sq_to_K]; norm_cast

/-- The physical bilinear mass is the squared first-component L² norm. -/
theorem periodOneSobolevMass_real_eq (a : realTypeSobolevSourceLocus) :
    periodOneSobolevMass a.val = (‖scalarInclusion a.val.1‖^2 : ℝ) := by
  have hb : scalarInclusion a.val.2 = star (Coeff.reflection (scalarInclusion a.val.1)) := by
    ext n
    exact a.property n
  rw [periodOneSobolevMass,hb,pairing_star_self,Coeff.reflection.norm_map]

/-- The kinetic part is nonnegative and equals the physical derivative norm. -/
theorem periodOneSobolevKinetic_real_eq (a : realTypeSobolevSourceLocus) :
    periodOneSobolevKinetic a.val = (‖periodOneDerivative a.val.1‖^2 : ℝ) := by
  have hb : periodOneDerivative a.val.2 = star (Coeff.reflection (periodOneDerivative a.val.1)) := by
    ext n
    have hr : scalarInclusion a.val.2 n = conj (scalarInclusion a.val.1 (-n)) := a.property n
    simp only [scalarInclusion_apply] at hr
    change periodOneDerivative a.val.2 n = conj (periodOneDerivative a.val.1 (-n))
    rw [periodOneDerivative_apply,periodOneDerivative_apply,hr]
    have htwo : conj (2 : ℂ) = 2 := map_ofNat (starRingEnd ℂ) 2
    simp [map_mul,htwo]
  rw [periodOneSobolevKinetic,hb,pairing_star_self,Coeff.reflection.norm_map]

/-- H¹ synthesis preserves the physical conjugate-pair condition. -/
theorem periodOneSobolevSynthesis_real (a : realTypeSobolevSourceLocus) (x : ℝ) :
    periodOneSobolevSynthesis a.val.2 (x : AddCircle (2 : ℝ)) =
      conj (periodOneSobolevSynthesis a.val.1 (x : AddCircle (2 : ℝ))) := by
  let H := fun b : realTypeSobolevSourceLocus =>
    periodOneSobolevSynthesis b.val.2 (x : AddCircle (2 : ℝ)) -
      conj (periodOneSobolevSynthesis b.val.1 (x : AddCircle (2 : ℝ)))
  have hc : Continuous H := by unfold H; fun_prop
  apply sub_eq_zero.mp
  apply eq_of_continuousOn_of_sourceSobolevFiniteGap isOpen_univ hc.continuousOn 0 _ a (mem_univ a)
  intro b _ hf
  let φ : realTypeSourceSubmodule 2 := ⟨sobolevSourceInclusion b.val,b.property⟩
  have he : sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf = b.val :=
    sourceFiniteGapSobolevPair_sobolevSource b hf
  have hp := periodOneSobolevSynthesis_sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf
  rw [he] at hp
  change periodOneSobolevSynthesis b.val.2 (x : AddCircle (2 : ℝ)) -
    conj (periodOneSobolevSynthesis b.val.1 (x : AddCircle (2 : ℝ))) = 0
  rw [congrFun hp.1 x,congrFun hp.2 x]
  exact sub_eq_zero.mpr (sourceFiniteGapPhysicalPair_real (by simp) (by norm_num) φ hf x)

/-- The defocusing quartic interaction is nonnegative on the full real H¹ locus. -/
theorem periodOneSobolevQuartic_real_nonneg (a : realTypeSobolevSourceLocus) :
    0 ≤ (periodOneSobolevQuartic a.val).re := by
  rw [periodOneSobolevQuartic_eq_integral]
  have hi := (((continuous_periodOneSobolevSynthesis a.val.1).pow 2).mul
    ((continuous_periodOneSobolevSynthesis a.val.2).pow 2)).intervalIntegrable (μ := volume) 0 1
  have he := (intervalIntegral.intervalIntegral_re hi).symm
  change (∫ x in (0 : ℝ)..1, (periodOneSobolevSynthesis a.val.1 (x : AddCircle (2 : ℝ)))^2 *
    (periodOneSobolevSynthesis a.val.2 (x : AddCircle (2 : ℝ)))^2).re = _ at he
  rw [he]
  apply intervalIntegral.integral_nonneg (by norm_num : (0 : ℝ) ≤ 1)
  intro x _
  change 0 ≤ ((periodOneSobolevSynthesis a.val.1 (x : AddCircle (2 : ℝ)))^2 *
    (periodOneSobolevSynthesis a.val.2 (x : AddCircle (2 : ℝ)))^2).re
  rw [periodOneSobolevSynthesis_real]
  have hz (z : ℂ) : (z^2*conj z^2).re = ‖z‖^4 := by
    calc
      _ = (‖z‖^2)^2 := by rw [← mul_pow,Complex.mul_conj']; norm_cast
      _ = _ := by ring
  rw [hz]
  positivity

/-- The first H¹ component is controlled by conserved mass and defocusing energy. -/
theorem norm_sobolev_fst_sq_le_mass_energy (a : realTypeSobolevSourceLocus) :
    ‖a.val.1‖^2 ≤ 2*((periodOneSobolevMass a.val).re + (periodOneSobolevHamiltonian a.val).re) := by
  have h := norm_scalarSobolev_sq_le a.val.1
  rw [periodOneSobolevMass_real_eq,ofReal_re,periodOneSobolevHamiltonian,
    add_re,periodOneSobolevKinetic_real_eq,ofReal_re]
  linarith [periodOneSobolevQuartic_real_nonneg a]

/-- An explicit continuous amplitude bound depending only on mass and energy. -/
def sobolevEnergyAmplitude (a : ScalarDomain 2 × ScalarDomain 2) : ℝ :=
  ‖periodOneSobolevSynthesis‖ *
    Real.sqrt (2*((periodOneSobolevMass a).re+(periodOneSobolevHamiltonian a).re))

theorem sobolevEnergyAmplitude_nonneg (a : ScalarDomain 2 × ScalarDomain 2) :
    0 ≤ sobolevEnergyAmplitude a := mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)

theorem continuous_sobolevEnergyAmplitude : Continuous sobolevEnergyAmplitude := by
  unfold sobolevEnergyAmplitude
  exact continuous_const.mul ((continuous_const.mul
    ((Complex.continuous_re.comp continuous_periodOneSobolevMass).add
      (Complex.continuous_re.comp continuous_periodOneSobolevHamiltonian))).sqrt)

/-- Physical mass and defocusing energy bound the uniform spatial amplitude. -/
theorem norm_periodOneSobolevSynthesis_le_energy (a : realTypeSobolevSourceLocus) :
    ‖periodOneSobolevSynthesis a.val.1‖ ≤ sobolevEnergyAmplitude a.val := by
  exact (periodOneSobolevSynthesis.le_opNorm a.val.1).trans
    (mul_le_mul_of_nonneg_left (Real.le_sqrt_of_sq_le (norm_sobolev_fst_sq_le_mass_energy a))
      (norm_nonneg _))

end NLS.ZakharovShabat
