import NLS.Fourier.ShiftedRudinShapiro
import Mathlib.Analysis.PSeries

/-!
# Lemma A.5: a continuous function outside every FLᵖ below two

A uniformly convergent series of disjoint Rudin–Shapiro blocks gives one
continuous function whose coefficients lie in no ℓᵖ with 1 ≤ p < 2.
The block amplitudes are 1/((j+1)^2*2^j). Their uniform norms are summable,
whereas their ℓᵖ norms grow exponentially when p < 2.

This proves the source's existential assertion by an alternative construction;
it does not analyze the particular oscillatory series printed in its proof.
The final theorem concerns the original periodic distribution of this function.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal ZeroAtInfty
namespace NLS.Fourier
variable {L : ℝ} [Fact (0 < L)]

/-- The jth term of the uniformly convergent counterexample series. -/
def continuousCounterexampleTerm (j : ℕ) : C(AddCircle L,ℂ) :=
  (((((j+1:ℕ):ℝ)^2 * (2:ℝ)^j)⁻¹ : ℝ) : ℂ) • shiftedRudinShapiro j

/-- A summable inverse-square bound for the uniform norm of each term. -/
theorem norm_continuousCounterexampleTerm_le (j : ℕ) :
    ‖continuousCounterexampleTerm (L := L) j‖ ≤ Real.sqrt 2 * (((j+1:ℕ):ℝ)^2)⁻¹ := by
  rw [continuousCounterexampleTerm,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  calc
    _ ≤ (((j+1:ℕ):ℝ)^2 * (2:ℝ)^j)⁻¹ * (Real.sqrt 2 * (2:ℝ)^j) := by
      gcongr
      exact norm_shiftedRudinShapiro_le j
    _ = _ := by field_simp

/-- The series converges absolutely in the Banach space of continuous functions. -/
theorem summable_norm_continuousCounterexampleTerm :
    Summable (fun j : ℕ => ‖continuousCounterexampleTerm (L := L) j‖) := by
  have hs : Summable (fun j : ℕ => (((j+1:ℕ):ℝ)^2)⁻¹) := by
    simpa only [one_div] using (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2:ℕ)))
  exact (hs.mul_left (Real.sqrt 2)).of_nonneg_of_le (fun j => norm_nonneg _) norm_continuousCounterexampleTerm_le

/-- One continuous witness for all the exponents in Lemma A.5. -/
def continuousFourierCounterexample : C(AddCircle L,ℂ) := ∑' j : ℕ, continuousCounterexampleTerm j

/-- Fourier extraction commutes with the uniformly convergent block series. -/
theorem continuousFourierCounterexample_fourierCoeff (k : ℤ) :
    fourierCoeff (continuousFourierCounterexample (L := L)) k = ∑' j : ℕ, fourierCoeff (continuousCounterexampleTerm (L := L) j) k := by
  let F : C(AddCircle L,ℂ) →L[ℂ] ℂ := (circleLpCoefficient (L := L) (q := 1) k).comp (ContinuousMap.toLp (E := ℂ) 1 (AddCircle.haarAddCircle (T := L)) ℂ)
  have hF (f : C(AddCircle L,ℂ)) : F f = fourierCoeff f k := by
    change fourierCoeff (ContinuousMap.toLp 1 AddCircle.haarAddCircle ℂ f) k = _
    rw [fourierCoeff_congr_ae (ContinuousMap.coeFn_toLp _ _)]
  rw [← hF]
  change F (∑' j : ℕ, continuousCounterexampleTerm j) = _
  rw [F.map_tsum (summable_norm_continuousCounterexampleTerm (L := L)).of_norm]
  simp only [hF]

/-- Each frequency in a block receives a contribution from that block alone. -/
theorem continuousFourierCounterexample_block_coefficient (j : ℕ) (k : ℤ)
    (hk : (4^j:ℕ) ≤ k ∧ k < 2*(4^j:ℕ)) :
    fourierCoeff (continuousFourierCounterexample (L := L)) k =
      (((((j+1:ℕ):ℝ)^2 * (2:ℝ)^j)⁻¹ : ℝ) : ℂ) * fourierCoeff (shiftedRudinShapiro (L := L) j) k := by
  rw [continuousFourierCounterexample_fourierCoeff]
  rw [tsum_eq_single j]
  · simp only [continuousCounterexampleTerm,ContinuousMap.coe_smul,fourierCoeff.const_smul,smul_eq_mul]
  · intro i hi
    have hn := shiftedRudinShapiro_blocks_disjoint (Ne.symm hi) k hk
    have hz : fourierCoeff (shiftedRudinShapiro (L := L) i) k = 0 := by
      apply norm_eq_zero.mp
      rw [shiftedRudinShapiro_coeff_norm,if_neg hn]
    simp only [continuousCounterexampleTerm,ContinuousMap.coe_smul,fourierCoeff.const_smul,smul_eq_mul,hz,mul_zero]

/-- The finite coefficient block as an element of the Banach sequence space. -/
def continuousCounterexampleBlock (p : ℝ≥0∞) [Fact (1 ≤ p)] (j : ℕ) : Coeff p :=
  (((((j+1:ℕ):ℝ)^2 * (2:ℝ)^j)⁻¹ : ℝ) : ℂ) •
    Coeff.shift (4^j:ℕ) (Coeff.ofFinsupp (rudinShapiroCoefficients (L := L) (2*j)))

/-- The coefficient block is the actual Fourier sequence of its continuous term. -/
theorem continuousCounterexampleBlock_apply (p : ℝ≥0∞) [Fact (1 ≤ p)] (j : ℕ) (k : ℤ) :
    continuousCounterexampleBlock (L := L) p j k = fourierCoeff (continuousCounterexampleTerm (L := L) j) k := by
  simp only [continuousCounterexampleBlock,lp.coeFn_smul,Pi.smul_apply,Coeff.shift_apply,
    Coeff.ofFinsupp_apply,rudinShapiroCoefficients_apply,continuousCounterexampleTerm,
    ContinuousMap.coe_smul,fourierCoeff.const_smul,shiftedRudinShapiro,fourierCoeff_fourier_mul,smul_eq_mul]

/-- Any full coefficient sequence in ℓᵖ bounds the norm of each disjoint block. -/
theorem norm_continuousCounterexampleBlock_le {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (a : Coeff p) (ha : ∀ k, a k = fourierCoeff (continuousFourierCounterexample (L := L)) k) (j : ℕ) :
    ‖continuousCounterexampleBlock (L := L) p j‖ ≤ ‖a‖ := by
  apply lp.norm_mono (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  intro k
  by_cases hk : (4^j:ℕ) ≤ k ∧ k < 2*(4^j:ℕ)
  · rw [continuousCounterexampleBlock_apply,ha,continuousFourierCounterexample_block_coefficient j k hk]
    simp only [continuousCounterexampleTerm,ContinuousMap.coe_smul,fourierCoeff.const_smul,smul_eq_mul]
    rfl
  · have hz : fourierCoeff (shiftedRudinShapiro (L := L) j) k = 0 := by
      apply norm_eq_zero.mp
      rw [shiftedRudinShapiro_coeff_norm,if_neg hk]
    rw [continuousCounterexampleBlock_apply]
    simp only [continuousCounterexampleTerm,ContinuousMap.coe_smul,fourierCoeff.const_smul,smul_eq_mul,hz,mul_zero,norm_zero]
    exact norm_nonneg _

/-- The exact coefficient norm exhibits the exponential growth below two. -/
theorem norm_continuousCounterexampleBlock {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : 0 < p.toReal) (j : ℕ) :
    ‖continuousCounterexampleBlock (L := L) p j‖ =
      ((2:ℝ)^(2/p.toReal-1))^j / ((j+1:ℕ):ℝ)^2 := by
  rw [continuousCounterexampleBlock,norm_smul,Coeff.norm_shift,norm_rudinShapiroCoefficients hp,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have hpow : (((2:ℝ)^(2*j))^(1/p.toReal)) = ((2:ℝ)^(2/p.toReal))^j := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
      ← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    push_cast
    ring
  rw [hpow,Real.rpow_sub (by norm_num : (0:ℝ) < 2),Real.rpow_one,div_pow]
  field_simp

/-- The single continuous witness has coefficients in no ℓᵖ below two. -/
theorem continuousFourierCounterexample_not_memℓp {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp₂ : p < 2) :
    ¬Memℓp (fourierCoeff (continuousFourierCounterexample (L := L))) p := by
  intro hm
  let a : Coeff p := ⟨fourierCoeff (continuousFourierCounterexample (L := L)),hm⟩
  have hpt : p ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) hp₂.le
  have hp : 0 < p.toReal := (ENNReal.toReal_pos_iff_ne_top p).mpr hpt
  have hp₂r : p.toReal < 2 := by
    simpa only [ENNReal.toReal_ofNat] using (ENNReal.toReal_lt_toReal hpt (by norm_num)).mpr hp₂
  let r : ℝ := 2^(2/p.toReal-1)
  have hr : 1 < r := Real.one_lt_rpow (by norm_num) (by
    have h : (1:ℝ) < 2/p.toReal := (lt_div_iff₀ hp).mpr (by simpa only [one_mul] using hp₂r)
    linarith)
  have hb (j : ℕ) : r^j / ((j+1:ℕ):ℝ)^2 ≤ ‖a‖ := by
    rw [← norm_continuousCounterexampleBlock (L := L) hp j]
    exact norm_continuousCounterexampleBlock_le a (fun _ => rfl) j
  have hbase := ((tendsto_pow_const_div_const_pow_of_one_lt 2 hr).comp (tendsto_add_atTop_nat 1)).const_mul (‖a‖*r)
  have ht : Tendsto (fun j : ℕ => ‖a‖ * (((j+1:ℕ):ℝ)^2 / r^j)) atTop (𝓝 0) := by
    convert hbase using 1
    · funext j
      simp only [Function.comp_apply,pow_succ]
      field_simp [hr.ne',ne_of_gt (zero_lt_one.trans hr)]
    · simp
  have hone (j : ℕ) : 1 ≤ ‖a‖ * (((j+1:ℕ):ℝ)^2 / r^j) := by
    have h := (div_le_iff₀ (by positivity : (0:ℝ) < ((j+1:ℕ):ℝ)^2)).mp (hb j)
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (pow_pos (zero_lt_one.trans hr) j)).mpr
    simpa only [one_mul,mul_div_assoc] using h
  have hlim : (1:ℝ) ≤ 0 := ge_of_tendsto ht (Filter.Eventually.of_forall hone)
  norm_num at hlim

/-- The obstruction holds in the original distribution-based Fourier–Lebesgue space. -/
theorem continuousFourierCounterexample_not_fourierLebesgue {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp₂ : p < 2) :
    SmoothPeriodicTest.Distribution.ofContinuous (continuousFourierCounterexample (L := L)) ∉
      periodicFourierLebesgueSubmodule Weight.one p := by
  intro h
  apply continuousFourierCounterexample_not_memℓp (L := L) hp₂
  change Memℓp (fun k => (Weight.one k : ℂ) *
    SmoothPeriodicTest.Distribution.ofContinuous (continuousFourierCounterexample (L := L)) (SmoothPeriodicTest.mode (-k))) p at h
  simpa only [Weight.one_apply,Complex.ofReal_one,one_mul,SmoothPeriodicTest.Distribution.ofContinuous_coefficient] using h

/-- Lemma A.5, with one continuous witness independent of the exponent. -/
theorem exists_continuous_not_fourierLebesgue_below_two :
    ∃ f : C(AddCircle L,ℂ), ∀ p : ℝ≥0∞, 1 ≤ p → p < 2 →
      SmoothPeriodicTest.Distribution.ofContinuous f ∉ periodicFourierLebesgueSubmodule Weight.one p := by
  refine ⟨continuousFourierCounterexample,fun p hp hp₂ => ?_⟩
  let : Fact (1 ≤ p) := ⟨hp⟩
  exact continuousFourierCounterexample_not_fourierLebesgue hp₂

end NLS.Fourier
