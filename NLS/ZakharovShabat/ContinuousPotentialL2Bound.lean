import NLS.ZakharovShabat.ContinuousPotentialL2Class

/-! # Bounded inclusion of continuous interval potentials into physical L2

The established physical class map is bounded for the supremum curve
norm. This upgrades its existing linear map to a continuous linear map,
so physical spectral neighborhoods can be pulled back in that norm.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open NLS.LinearVolterra
namespace NLS.ZakharovShabat

theorem norm_continuousPotentialL2Class_le_two_norm (φ : Curve (ℂ × ℂ)) :
    ‖continuousPotentialL2Class φ‖ ≤ 2*‖φ‖ := by
  have hbound (g : ℝ → ℂ) (hg : Continuous g) (hb : ∀ s, ‖g s‖ ≤ ‖φ‖) :
      (∫ s in (0 : ℝ)..1, ‖g s‖^2) ≤ ‖φ‖^2 := by
    calc
      _ ≤ ∫ s in (0 : ℝ)..1, ‖φ‖^2 :=
        intervalIntegral.integral_mono_on (by norm_num)
          ((hg.norm.pow 2).intervalIntegrable 0 1) (continuous_const.intervalIntegrable 0 1)
          (fun s _ => pow_le_pow_left₀ (norm_nonneg _) (hb s) 2)
      _ = _ := by simp
  have h1 := hbound (fun s => (extend φ s).1) (continuous_extend φ).fst
    (fun s => (norm_fst_le (extend φ s)).trans (φ.norm_coe_le_norm _))
  have h2 := hbound (fun s => (extend φ s).2) (continuous_extend φ).snd
    (fun s => (norm_snd_le (extend φ s)).trans (φ.norm_coe_le_norm _))
  have he : ‖continuousPotentialL2Class φ‖^2 =
      (∫ s in (0 : ℝ)..1, ‖(extend φ s).1‖^2) +
        ∫ s in (0 : ℝ)..1, ‖(extend φ s).2‖^2 := norm_sq_intervalL2OfFunction _ _
  nlinarith [norm_nonneg (continuousPotentialL2Class φ),norm_nonneg φ,sq_nonneg ‖φ‖]

/-- The same actual physical L2 class, now as a bounded complex-linear map. -/
def continuousPotentialL2CLM : Curve (ℂ × ℂ) →L[ℂ] IntervalPairL2 :=
  continuousPotentialL2LinearMap.mkContinuous 2 norm_continuousPotentialL2Class_le_two_norm

@[simp] theorem continuousPotentialL2CLM_apply (φ : Curve (ℂ × ℂ)) :
    continuousPotentialL2CLM φ = continuousPotentialL2Class φ := rfl

end NLS.ZakharovShabat
