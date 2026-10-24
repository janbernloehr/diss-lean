import NLS.ZakharovShabat.L2WholeLineDifferentialEquation

/-! # The periodic potential retains its physical L2 norm on every period -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
namespace NLS.ZakharovShabat

/-- Periodization recovers the original potential class on the unit interval. -/
theorem l2WholeLinePotential_ae_unit (u : IntervalPairL2) :
    l2WholeLinePotential u =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] intervalL2Representative u := by
  have hne : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1), s ≠ (1 : ℝ) :=
    ae_restrict_of_ae (by simp [ae_iff])
  filter_upwards [ae_restrict_mem measurableSet_Ioc,hne] with s hs hn
  simp only [l2WholeLinePotential,Int.fract_eq_self.mpr ⟨hs.1.le,lt_of_le_of_ne hs.2 hn⟩]

theorem memLp_l2WholeLinePotential_unit (u : IntervalPairL2) :
    MemLp (l2WholeLinePotential u) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
  (memLp_congr_ae (l2WholeLinePotential_ae_unit u)).mpr (memLp_intervalL2Representative u)

/-- Translation identifies any integer period with the original physical measure space. -/
theorem measurePreserving_period_sub_int (n : ℤ) :
    MeasurePreserving (fun t : ℝ => t-(n : ℝ))
      (volume.restrict (Ioc (n : ℝ) ((n : ℝ)+1)))
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have h := (measurePreserving_sub_right volume (n : ℝ)).restrict_preimage (s := Ioc (0 : ℝ) 1) measurableSet_Ioc
  have he : (fun t : ℝ => t-(n : ℝ)) ⁻¹' Ioc (0 : ℝ) 1 = Ioc (n : ℝ) ((n : ℝ)+1) := by
    ext t
    simp only [mem_preimage,mem_Ioc]
    constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
  rwa [he] at h

theorem l2WholeLinePotential_comp_sub_int (u : IntervalPairL2) (n : ℤ) :
    l2WholeLinePotential u ∘ (fun t : ℝ => t-(n : ℝ)) = l2WholeLinePotential u := by
  funext t
  simpa only [Function.comp_def,Int.cast_neg,sub_eq_add_neg] using
    l2WholeLinePotential_add_int u t (-n)

/-- The actual periodized potential is square integrable on every positive or negative period. -/
theorem memLp_l2WholeLinePotential_period (u : IntervalPairL2) (n : ℤ) :
    MemLp (l2WholeLinePotential u) 2 (volume.restrict (Ioc (n : ℝ) ((n : ℝ)+1))) := by
  have h := (memLp_l2WholeLinePotential_unit u).comp_measurePreserving
    (measurePreserving_period_sub_int n)
  rwa [l2WholeLinePotential_comp_sub_int] at h

/-- The physical L2 seminorm is exactly the same on every integer period. -/
theorem eLpNorm_l2WholeLinePotential_period (u : IntervalPairL2) (n : ℤ) :
    eLpNorm (l2WholeLinePotential u) 2 (volume.restrict (Ioc (n : ℝ) ((n : ℝ)+1))) =
      eLpNorm (intervalL2Representative u) 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have h := eLpNorm_comp_measurePreserving (p := 2)
    (memLp_l2WholeLinePotential_unit u).aestronglyMeasurable (measurePreserving_period_sub_int n)
  rw [l2WholeLinePotential_comp_sub_int] at h
  exact h.trans (eLpNorm_congr_ae (l2WholeLinePotential_ae_unit u))

end NLS.ZakharovShabat
