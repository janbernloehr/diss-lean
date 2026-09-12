import NLS.Fourier.FractionalHardyPreestimate

/-!
# Left endpoint fractional Hardy inequality

Positive-distance cutoffs give finite weighted energies for arbitrary `L²`
data. The contracting preestimate can therefore be absorbed legitimately.
Monotone convergence removes the cutoff without presupposing boundary regularity.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NLS.Fourier

/-- The half interval away from the left endpoint contributes only the `L²` term. -/
theorem leftBoundaryEnergy_split_le {s δ L : ℝ} (hs : 0 ≤ s) (hδ : 0 ≤ δ) (hL : 0 < L)
    (f : ℝ → ℂ) (hf : Measurable f) :
    leftBoundaryEnergy s δ L f ≤ leftBoundaryEnergy s δ (L / 2) f +
      ENNReal.ofReal ((L / 2) ^ (-2 * s)) * ∫⁻ x : ℝ in Ioo 0 L, ENNReal.ofReal (‖f x‖ ^ 2) := by
  let w := fun x : ℝ => ENNReal.ofReal (x ^ (-2 * s)) * ENNReal.ofReal (‖f x‖ ^ 2)
  let g := fun x : ℝ => ENNReal.ofReal (‖f x‖ ^ 2)
  have hw : Measurable w := by dsimp [w]; fun_prop
  calc
    _ = ∫⁻ x : ℝ, (Ioo δ L).indicator w x := (lintegral_indicator measurableSet_Ioo _).symm
    _ ≤ ∫⁻ x : ℝ, (Ioo δ (L / 2)).indicator w x +
        ENNReal.ofReal ((L / 2) ^ (-2 * s)) * (Ioo 0 L).indicator g x := by
      apply lintegral_mono
      intro x
      dsimp only
      by_cases hx : x ∈ Ioo δ L
      · rw [indicator_of_mem hx]
        by_cases hx₂ : x < L / 2
        · rw [indicator_of_mem (show x ∈ Ioo δ (L / 2) from ⟨hx.1, hx₂⟩)]
          exact le_add_of_nonneg_right zero_le
        · rw [indicator_of_notMem (show x ∉ Ioo δ (L / 2) from fun h => hx₂ h.2), zero_add,
            indicator_of_mem (show x ∈ Ioo 0 L from ⟨hδ.trans_lt hx.1, hx.2⟩)]
          exact mul_le_mul' (ENNReal.ofReal_le_ofReal
            (Real.rpow_le_rpow_of_nonpos (by positivity) (le_of_not_gt hx₂) (by linarith))) le_rfl
      · rw [indicator_of_notMem hx]
        exact zero_le
    _ = _ := by
      rw [lintegral_add_left (hw.indicator measurableSet_Ioo),
        lintegral_indicator measurableSet_Ioo, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_indicator measurableSet_Ioo]
      rfl

/-- Legitimate absorption of a finite extended-nonnegative quantity. -/
theorem ennreal_absorb_finite {a J B : ℝ≥0∞} (hJ : J < ⊤) (h : J ≤ a * J + B) :
    (1 - a) * J ≤ B := by
  rw [ENNReal.sub_mul (fun _ _ => hJ.ne), one_mul]
  exact tsub_le_iff_left.mpr h

/-- A uniform coercive estimate for every positive cutoff. -/
theorem leftBoundaryEnergy_cutoff_bound {s δ L : ℝ} (hs : 0 < s) (hs₁ : s < 1 / 2)
    (hδ : 0 < δ) (hL : 0 < L) (f : ℝ → ℂ) (hf : Measurable f)
    (hf₂ : MemLp f 2 (volume.restrict (Ioo 0 L))) :
    (1 - ENNReal.ofReal ((1 + hardyAveragingConstant s) / 2)) * leftBoundaryEnergy s δ L f ≤
      ENNReal.ofReal (1 + 1 / hardyAbsorptionParameter s) * fractionalIntervalEnergy s L f +
        ENNReal.ofReal ((L / 2) ^ (-2 * s)) * ∫⁻ x : ℝ in Ioo 0 L, ENNReal.ofReal (‖f x‖ ^ 2) := by
  apply ennreal_absorb_finite (leftBoundaryEnergy_lt_top hs.le hδ f hf₂)
  have h := (leftBoundaryEnergy_split_le hs.le hδ.le hL f hf).trans
    (add_le_add_left (leftBoundaryEnergy_preestimate_contracting hs hs₁ hδ.le f hf) _)
  simpa only [add_assoc] using h

/-- Increasing positive cutoffs exhaust the open interval. -/
theorem iUnion_hardy_cutoffs (L : ℝ) :
    (⋃ n : ℕ, Ioo (1 / ((n : ℝ) + 1)) L) = Ioo 0 L := by
  ext x
  simp only [mem_iUnion, mem_Ioo]
  constructor
  · rintro ⟨n, hn, hx⟩
    exact ⟨lt_trans (by positivity) hn, hx⟩
  · rintro ⟨hx, hL⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx
    exact ⟨n, hn, hL⟩

/-- The full endpoint energy is the supremum of the finite-cutoff energies. -/
theorem leftBoundaryEnergy_eq_iSup (s L : ℝ) (f : ℝ → ℂ) :
    leftBoundaryEnergy s 0 L f = ⨆ n : ℕ, leftBoundaryEnergy s (1 / ((n : ℝ) + 1)) L f := by
  unfold leftBoundaryEnergy
  rw [← iUnion_hardy_cutoffs L]
  apply setLIntegral_iUnion_of_directed
  apply Monotone.directed_le
  intro m n hmn
  apply Ioo_subset_Ioo _ le_rfl
  exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)

/-- The left fractional Hardy inequality for arbitrary measurable interval `L²` data. -/
theorem leftBoundaryEnergy_hardy_bound {s L : ℝ} (hs : 0 < s) (hs₁ : s < 1 / 2)
    (hL : 0 < L) (f : ℝ → ℂ) (hf : Measurable f)
    (hf₂ : MemLp f 2 (volume.restrict (Ioo 0 L))) :
    (1 - ENNReal.ofReal ((1 + hardyAveragingConstant s) / 2)) * leftBoundaryEnergy s 0 L f ≤
      ENNReal.ofReal (1 + 1 / hardyAbsorptionParameter s) * fractionalIntervalEnergy s L f +
        ENNReal.ofReal ((L / 2) ^ (-2 * s)) * ∫⁻ x : ℝ in Ioo 0 L, ENNReal.ofReal (‖f x‖ ^ 2) := by
  rw [leftBoundaryEnergy_eq_iSup, ENNReal.mul_iSup]
  apply iSup_le
  intro n
  exact leftBoundaryEnergy_cutoff_bound hs hs₁ (by positivity) hL f hf hf₂

/-- Finite intrinsic fractional energy and `L²` imply finite left boundary energy below half. -/
theorem leftBoundaryEnergy_lt_top_of_interval {s L : ℝ} (hs : 0 < s) (hs₁ : s < 1 / 2)
    (hL : 0 < L) (f : ℝ → ℂ) (hf : Measurable f)
    (hf₂ : MemLp f 2 (volume.restrict (Ioo 0 L))) (hE : fractionalIntervalEnergy s L f < ⊤) :
    leftBoundaryEnergy s 0 L f < ⊤ := by
  have hc : ENNReal.ofReal ((1 + hardyAveragingConstant s) / 2) < 1 := by
    rw [ENNReal.ofReal_lt_one]
    linarith [hardyAveragingConstant_lt_one hs hs₁]
  have ha : (1 - ENNReal.ofReal ((1 + hardyAveragingConstant s) / 2)) ≠ 0 :=
    (tsub_pos_iff_lt.mpr hc).ne'
  have hi : Integrable (fun x => ‖f x‖ ^ 2) (volume.restrict (Ioo 0 L)) :=
    hf₂.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hn : (∫⁻ x : ℝ in Ioo 0 L, ENNReal.ofReal (‖f x‖ ^ 2)) < ⊤ :=
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).mp hi.2
  have hb := (leftBoundaryEnergy_hardy_bound hs hs₁ hL f hf hf₂).trans_lt
    (ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hE,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hn⟩)
  rcases ENNReal.mul_lt_top_iff.mp hb with h | h | h
  · exact h.2
  · exact (ha h).elim
  · rw [h]
    exact ENNReal.zero_lt_top

end NLS.Fourier
