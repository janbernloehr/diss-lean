import NLS.Articles.KdVKdV2Frequencies.SignedMassDivergence
import NLS.SequenceSpaces.WeightedSingle
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Finite signed perturbations with a prescribed KdV mass increment

The perturbation is placed at the two modes ±(N+1), outside a symmetric
truncation. Its contribution to H0 is exactly (2(N+1)pi)r²; the two signed
coordinates represent one positive action, so no extra factor two occurs.
-/

noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies

/-- A real conjugate pair at two nonzero opposite modes. -/
def signedNeedle (w : Weight) (m : ℕ) (hm : 1 ≤ m) (r : ℝ) : SignedCoordinates w 2 :=
  ⟨WeightedCoeff.single w (m : ℤ) (r : ℂ) + WeightedCoeff.single w (-(m : ℤ)) (r : ℂ), by
    have h0 : (m : ℤ) ≠ 0 := by omega
    have hneg : (m : ℤ) ≠ -(m : ℤ) := by omega
    constructor
    · simp only [WeightedCoeff.add_val, WeightedCoeff.single_val, Pi.single_apply,
        if_neg (Ne.symm h0), if_neg (Ne.symm (neg_ne_zero.mpr h0)), add_zero]
    · intro k
      by_cases hpos : k = (m : ℤ)
      · subst k
        simp [WeightedCoeff.single_val, hneg, Ne.symm hneg]
      · by_cases hminus : k = -(m : ℤ)
        · subst k
          simp [WeightedCoeff.single_val, hneg, Ne.symm hneg]
        · have hpos' : -k ≠ (m : ℤ) := by omega
          have hminus' : -k ≠ -(m : ℤ) := by omega
          simp [WeightedCoeff.single_val, hpos, hminus, hpos', hminus']⟩

theorem signedNeedle_pos (w : Weight) (m : ℕ) (hm : 1 ≤ m) (r : ℝ) (j : ℕ) :
    (signedNeedle w m hm r).val.val (j : ℤ) = if j = m then (r : ℂ) else 0 := by
  have hneg : (j : ℤ) ≠ -(m : ℤ) := by omega
  simp [signedNeedle, WeightedCoeff.single_val, Pi.single_apply, hneg]

/-- Finite truncation plus a disjoint real needle. -/
def massInsertedTruncate (w : Weight) (N : ℕ) (a : SignedCoordinates w 2) (r : ℝ) :
    SignedCoordinates w 2 :=
  ⟨(signedTruncate w N a).val + (signedNeedle w (N + 1) (by omega) r).val,
    (signedTruncate w N a).property.add (signedNeedle w (N + 1) (by omega) r).property⟩

theorem massInsertedTruncate_pos (w : Weight) (N : ℕ) (a : SignedCoordinates w 2)
    (r : ℝ) (j : ℕ) :
    (massInsertedTruncate w N a r).val.val (j : ℤ) =
      (signedTruncate w N a).val.val (j : ℤ) + if j = N + 1 then (r : ℂ) else 0 := by
  exact congrArg ((signedTruncate w N a).val.val (j : ℤ) + ·)
    (signedNeedle_pos w (N + 1) (by omega) r j)

theorem hasHalfRegularity_massInsertedTruncate (w : Weight) (N : ℕ)
    (a : SignedCoordinates w 2) (r : ℝ) : HasHalfRegularity (massInsertedTruncate w N a r) := by
  apply hasHalfRegularity_of_finiteSupport
  apply (Finset.finite_toSet (Finset.Icc (-((N + 1 : ℕ) : ℤ)) (N + 1))).subset
  intro k hk
  change _ ≠ 0 at hk
  by_contra hnot
  apply hk
  have hsmall : k ∉ Finset.Icc (-(N : ℤ)) N := by
    simp only [Finset.mem_coe, Finset.mem_Icc] at hnot ⊢
    omega
  have hpos : k ≠ ((N + 1 : ℕ) : ℤ) := by
    simp only [Finset.mem_coe, Finset.mem_Icc] at hnot
    omega
  have hneg : k ≠ -((N + 1 : ℕ) : ℤ) := by
    simp only [Finset.mem_coe, Finset.mem_Icc] at hnot
    omega
  change (WeightedCoeff.truncate w 2 (Finset.Icc (-(N : ℤ)) N) a.val).val k +
    (WeightedCoeff.single w ((N + 1 : ℕ) : ℤ) (r : ℂ) +
      WeightedCoeff.single w (-((N + 1 : ℕ) : ℤ)) (r : ℂ)).val k = 0
  simp only [WeightedCoeff.truncate_apply, if_neg hsmall, WeightedCoeff.add_val,
    WeightedCoeff.single_val, Pi.single_apply, if_neg hpos, if_neg hneg, add_zero]

theorem kdvMassTerm_massInsertedTruncate (w : Weight) (N : ℕ)
    (a : SignedCoordinates w 2) (r : ℝ) (j : ℕ) :
    kdvMassTerm (massInsertedTruncate w N a r) j = kdvMassTerm (signedTruncate w N a) j +
      if j = N + 1 then (2 * ((N + 1 : ℕ) : ℝ) * Real.pi) * r ^ 2 else 0 := by
  by_cases hj : j = N + 1
  · subst j
    have hzero : (signedTruncate w N a).val.val ((N + 1 : ℕ) : ℤ) = 0 := by
      change (WeightedCoeff.truncate w 2 (Finset.Icc (-(N : ℤ)) N) a.val).val _ = 0
      rw [WeightedCoeff.truncate_apply, if_neg (by simp only [Finset.mem_Icc]; omega)]
    simp only [kdvMassTerm, massInsertedTruncate_pos, hzero, zero_add,
      norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
    simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  · simp only [kdvMassTerm, massInsertedTruncate_pos, if_neg hj, add_zero]

theorem kdvFiniteMass_massInsertedTruncate (w : Weight) (N : ℕ)
    (a : SignedCoordinates w 2) (r : ℝ) :
    kdvFiniteMass (massInsertedTruncate w N a r) = kdvFiniteMass (signedTruncate w N a) +
      (2 * ((N + 1 : ℕ) : ℝ) * Real.pi) * r ^ 2 := by
  unfold kdvFiniteMass
  simp_rw [kdvMassTerm_massInsertedTruncate]
  rw [((hasHalfRegularity_iff_summable_kdvMassTerm _).mp
    (hasHalfRegularity_signedTruncate w N a)).tsum_add
      ((hasSum_ite_eq (N + 1) _).summable)]
  simp

/-- The exact amplitude required to insert a positive mass D. -/
def massInsertionAmplitude (D : ℝ) (m : ℕ) : ℝ :=
  Real.sqrt (D / (2 * (m : ℝ) * Real.pi))

theorem massInsertionAmplitude_sq (D : ℝ) (hD : 0 ≤ D) (m : ℕ) (hm : 1 ≤ m) :
    (2 * (m : ℝ) * Real.pi) * massInsertionAmplitude D m ^ 2 = D := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  rw [massInsertionAmplitude, Real.sq_sqrt (by positivity)]
  field_simp

theorem kdvFiniteMass_prescribed_insert (w : Weight) (N : ℕ)
    (a : SignedCoordinates w 2) (D : ℝ) (hD : 0 ≤ D) :
    kdvFiniteMass (massInsertedTruncate w N a (massInsertionAmplitude D (N + 1))) =
      kdvFiniteMass (signedTruncate w N a) + D := by
  rw [kdvFiniteMass_massInsertedTruncate, massInsertionAmplitude_sq D hD _ (by omega)]

theorem norm_signedNeedle_le (w : Weight) (hw : ∀ k, w (-k) = w k)
    (m : ℕ) (hm : 1 ≤ m) (r : ℝ) :
    ‖(signedNeedle w m hm r).val‖ ≤ 2 * w (m : ℤ) * |r| := by
  change ‖WeightedCoeff.single w (m : ℤ) (r : ℂ) +
    WeightedCoeff.single w (-(m : ℤ)) (r : ℂ)‖ ≤ _
  calc
    _ ≤ ‖WeightedCoeff.single w (m : ℤ) (r : ℂ)‖ +
      ‖WeightedCoeff.single w (-(m : ℤ)) (r : ℂ)‖ := norm_add_le _ _
    _ = _ := by
      rw [WeightedCoeff.norm_single, WeightedCoeff.norm_single, hw]
      simp only [Complex.norm_real, Real.norm_eq_abs]
      ring

/-- The source Sobolev weight divided by sqrt(n) vanishes exactly in the
subcritical range required for the fixed-time mass perturbation. -/
theorem tendsto_sobolev_div_sqrt (σ : ℝ) (hσ : σ < 1 / 2) :
    Tendsto (fun m : ℕ => Weight.sobolev σ (m : ℤ) / Real.sqrt (m : ℝ)) atTop (𝓝 0) := by
  have hbase : Tendsto (fun m : ℕ => 1 + 1 / (m : ℝ)) atTop (𝓝 (1 : ℝ)) := by
    simpa only [add_zero] using (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add 1
  have hc : ContinuousAt (fun x : ℝ => x ^ σ) 1 :=
    Real.continuousAt_rpow_const 1 σ (Or.inl one_ne_zero)
  have hr : Tendsto (fun m : ℕ => (1 + 1 / (m : ℝ)) ^ σ) atTop (𝓝 (1 : ℝ)) := by
    simpa only [Real.one_rpow, Function.comp_def] using! hc.tendsto.comp hbase
  have hp : Tendsto (fun m : ℕ => (m : ℝ) ^ (σ - 1 / 2)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [neg_sub, Function.comp_def] using
      (tendsto_rpow_neg_atTop (sub_pos.mpr hσ)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hprod := hr.mul hp
  have he : (fun m : ℕ => Weight.sobolev σ (m : ℤ) / Real.sqrt (m : ℝ)) =ᶠ[atTop]
      (fun m => (1 + 1 / (m : ℝ)) ^ σ * (m : ℝ) ^ (σ - 1 / 2)) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hm' : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
    have hfactor : 1 + (m : ℝ) = (1 + 1 / (m : ℝ)) * (m : ℝ) := by
      field_simp
      ring
    simp only [Weight.sobolev_apply, Int.cast_natCast, abs_of_pos hm', Real.sqrt_eq_rpow]
    rw [hfactor, Real.mul_rpow (by positivity) hm'.le, div_eq_mul_inv,
      ← Real.rpow_neg hm'.le, mul_assoc, ← Real.rpow_add hm']
    congr 1
  have hzero : Tendsto (fun m : ℕ => (1 + 1 / (m : ℝ)) ^ σ * (m : ℝ) ^ (σ - 1 / 2))
      atTop (𝓝 0) := by simpa only [one_mul] using hprod
  exact hzero.congr' he.symm

theorem massInsertionAmplitude_factor (D : ℝ) (hD : 0 ≤ D) (m : ℕ) :
    massInsertionAmplitude D m = Real.sqrt (D / (2 * Real.pi)) / Real.sqrt (m : ℝ) := by
  unfold massInsertionAmplitude
  have he : D / (2 * (m : ℝ) * Real.pi) = (D / (2 * Real.pi)) / (m : ℝ) := by
    rw [div_div]
    congr 1
    ring
  rw [he, Real.sqrt_div (by positivity)]

theorem tendsto_sobolev_mul_massInsertionAmplitude (σ : ℝ) (hσ : σ < 1 / 2)
    (D : ℝ) (hD : 0 ≤ D) :
    Tendsto (fun m : ℕ => Weight.sobolev σ (m : ℤ) * massInsertionAmplitude D m)
      atTop (𝓝 0) := by
  have h := (tendsto_sobolev_div_sqrt σ hσ).const_mul (Real.sqrt (D / (2 * Real.pi)))
  have he (m : ℕ) : Weight.sobolev σ (m : ℤ) * massInsertionAmplitude D m =
      Real.sqrt (D / (2 * Real.pi)) * (Weight.sobolev σ (m : ℤ) / Real.sqrt (m : ℝ)) := by
    rw [massInsertionAmplitude_factor D hD]
    ring
  simpa only [← he, mul_zero] using h

/-- A fixed positive mass may be hidden in a norm-small high signed mode
precisely below the half-regularity threshold. -/
theorem tendsto_signedNeedle_zero (σ : ℝ) (hσ : σ < 1 / 2) (D : ℝ) (hD : 0 ≤ D) :
    Tendsto (fun N => (signedNeedle (Weight.sobolev σ) (N + 1) (by omega)
      (massInsertionAmplitude D (N + 1))).val) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h := ((tendsto_sobolev_mul_massInsertionAmplitude σ hσ D hD).comp
    (tendsto_add_atTop_nat 1)).const_mul 2
  apply squeeze_zero (fun N => norm_nonneg _)
  · intro N
    have hn := norm_signedNeedle_le (Weight.sobolev σ) (fun k => by simp)
      (N + 1) (by omega) (massInsertionAmplitude D (N + 1))
    simpa only [massInsertionAmplitude, abs_of_nonneg (Real.sqrt_nonneg _), mul_assoc] using hn
  · simpa only [Function.comp_def, mul_zero, mul_assoc, massInsertionAmplitude] using! h

theorem tendsto_massInsertedTruncate (σ : ℝ) (hσ : σ < 1 / 2)
    (a : SignedCoordinates (Weight.sobolev σ) 2) (D : ℝ) (hD : 0 ≤ D) :
    Tendsto (fun N => massInsertedTruncate (Weight.sobolev σ) N a
      (massInsertionAmplitude D (N + 1))) atTop (𝓝 a) := by
  apply tendsto_subtype_rng.mpr
  have hp := (continuous_subtype_val.tendsto a).comp (tendsto_signedTruncate (Weight.sobolev σ) a)
  have hq := tendsto_signedNeedle_zero σ hσ D hD
  simpa only [massInsertedTruncate, add_zero, Function.comp_def] using! hp.add hq

end NLS.Articles.KdVKdV2Frequencies
