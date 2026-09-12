import NLS.Fourier.FractionalRestriction
import NLS.Fourier.ArbitraryPeriodFourierLebesgue

/-!
# Intrinsic interval and periodic fractional Sobolev identification

Below half regularity, the physical periodic and intrinsic interval conditions
are equivalent. Actual interval Fourier integrals have weighted square
summability exactly when the original intrinsic energy is finite. The latter
criterion holds for every positive interval length.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NLS.Fourier

/-- The physical interval and periodic regularity conditions coincide below half. -/
theorem hasFractionalPeriodicRegularity_iff_intervalEnergy {s : ℝ}
    (hs : 0 < s) (hs₁ : s < 1 / 2) (f : CircleL2) :
    HasFractionalPeriodicRegularity s f ↔ fractionalIntervalEnergy s 2 (circlePullback f) < ⊤ :=
  ⟨fractionalIntervalEnergy_lt_top_of_periodic hs f, hasFractionalPeriodicRegularity_of_interval hs hs₁ f⟩

/-- Arbitrary interval representatives satisfy the exact weighted Fourier criterion below half. -/
theorem memlp_sobolev_periodTwoCoefficient_iff_intervalEnergy {s : ℝ}
    (hs : 0 < s) (hs₁ : s < 1 / 2) (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 2))) :
    Memℓp (fun n => (Weight.sobolev s n : ℂ) * periodTwoCoefficient f n) 2 ↔
      fractionalIntervalEnergy s 2 f < ⊤ := by
  refine ⟨?_, memlp_sobolev_periodTwoCoefficient_of_interval hs hs₁ f hf⟩
  intro ha
  let F := l2Synthesis (periodTwoL2Coefficients f hf)
  have hF : HasFractionalPeriodicRegularity s F := by
    rw [hasFractionalPeriodicRegularity_iff_memlp hs (by linarith)]
    simpa only [F, fourierCoeff_l2Synthesis, periodTwoL2Coefficients_apply] using ha
  have he : circlePullback F =ᵐ[volume.restrict (Ioo 0 2)] f := by
    simpa only [Measure.restrict_congr_set Ioo_ae_eq_Ioc] using circlePullback_periodTwoL2Coefficients f hf
  simpa only [fractionalIntervalEnergy_congr he] using fractionalIntervalEnergy_lt_top_of_periodic hs F hF

/-- Positive dilation preserves finiteness of the intrinsic fractional energy in both directions. -/
theorem fractionalIntervalEnergy_dilation_lt_top_iff {c : ℝ} (hc : 0 < c) (s L : ℝ) (f : ℝ → ℂ) :
    fractionalIntervalEnergy s L (intervalDilation c f) < ⊤ ↔ fractionalIntervalEnergy s (c * L) f < ⊤ := by
  rw [fractionalIntervalEnergy_dilation hc]
  constructor
  · intro h
    apply lt_top_iff_ne_top.mpr
    intro he
    rw [he, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hc _)).ne'] at h
    exact (lt_irrefl _ h)
  · exact fun h => ENNReal.mul_lt_top ENNReal.ofReal_lt_top h

/-- The intrinsic interval Sobolev criterion for the actual Fourier integrals on every positive period. -/
theorem memlp_sobolev_intervalFourierCoefficient_iff_intervalEnergy {L s : ℝ}
    (hL : 0 < L) (hs : 0 < s) (hs₁ : s < 1 / 2) (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 L))) :
    Memℓp (fun n => (Weight.sobolev s n : ℂ) * intervalFourierCoefficient L f n) 2 ↔
      fractionalIntervalEnergy s L f < ⊤ := by
  have h := memlp_sobolev_periodTwoCoefficient_iff_intervalEnergy hs hs₁
    (intervalDilation (L / 2) f) (memLp_periodTwoDilation hL f hf)
  rw [fractionalIntervalEnergy_dilation_lt_top_iff (by positivity : 0 < L / 2),
    div_mul_cancel₀ L (by norm_num : (2 : ℝ) ≠ 0)] at h
  simpa only [periodTwoCoefficient_intervalDilation hL] using h

/-- Finite intrinsic energy is equivalent to a unique actual weighted Fourier representation. -/
theorem intervalEnergy_lt_top_iff_existsUnique_sobolev {L s : ℝ}
    (hL : 0 < L) (hs : 0 < s) (hs₁ : s < 1 / 2) (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 L))) :
    fractionalIntervalEnergy s L f < ⊤ ↔
      ∃! a : WeightedCoeff (Weight.sobolev s) 2, ∀ n, a.val n = intervalFourierCoefficient L f n := by
  rw [← memlp_sobolev_intervalFourierCoefficient_iff_intervalEnergy hL hs hs₁ f hf]
  constructor
  · intro h
    refine ⟨⟨intervalFourierCoefficient L f, h⟩, (fun _ => rfl), ?_⟩
    intro a ha
    exact Subtype.ext (funext ha)
  · rintro ⟨a, ha, _⟩
    have h : Memℓp (fun n => (Weight.sobolev s n : ℂ) * a.val n) 2 := a.property
    simpa only [ha] using h

end NLS.Fourier
