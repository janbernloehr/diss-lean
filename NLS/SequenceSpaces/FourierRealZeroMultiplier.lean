import NLS.SequenceSpaces.FourierRealZeroSpatialGenerator

/-! Coefficient-preserving physical real weighted multipliers. A proved
conjugacy law makes the full real zero-mode projection inactive. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def fourierRealZeroMultiplier (w v : Weight) (hv : ∀ k, v (-k)=v k)
    (m : ℤ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ k, v k*‖m k‖ ≤ C*w k)
    (_hm : ∀ k, m (-k)=(starRingEnd ℂ) (m k)) :
    fourierRealZeroSubmodule w p →L[ℝ] fourierRealZeroSubmodule v p :=
  (fourierRealZeroFullProjection v hv).comp
    (((weightedMultiplierCLM w v m C hC hb).restrictScalars ℝ).comp
      (((zeroModeSubmodule w p).subtypeL.restrictScalars ℝ).comp (fourierRealZeroSubmodule w p).subtypeL))

theorem fourierRealZeroMultiplier_apply (w v : Weight) (hv : ∀ k, v (-k)=v k)
    (m : ℤ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ k, v k*‖m k‖ ≤ C*w k) (hm : ∀ k, m (-k)=(starRingEnd ℂ) (m k))
    (a : fourierRealZeroSubmodule w p) (k : ℤ) :
    (fourierRealZeroMultiplier w v hv m C hC hb hm a).val.val.val k=m k*a.val.val.val k := by
  let d := weightedMultiplierCLM w v m C hC hb a.val.val
  have h0 : d.val 0=0 := by
    change m 0*a.val.val.val 0=0
    rw [show a.val.val.val 0=0 from a.val.property,mul_zero]
  have hr (j : ℤ) : d.val (-j)=(starRingEnd ℂ) (d.val j) := by
    change m (-j)*a.val.val.val (-j)=(starRingEnd ℂ) (m j*a.val.val.val j)
    rw [hm,a.property,map_mul]
  have he := fourierRealZeroFullProjection_inclusion v hv (⟨⟨d,h0⟩,hr⟩ : fourierRealZeroSubmodule v p)
  change (fourierRealZeroFullProjection v hv d).val.val.val k= _
  rw [he]
  rfl

theorem norm_fourierRealZeroMultiplier_le (w v : Weight) (hv : ∀ k, v (-k)=v k)
    (m : ℤ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ k, v k*‖m k‖ ≤ C*w k) (hm : ∀ k, m (-k)=(starRingEnd ℂ) (m k))
    (a : fourierRealZeroSubmodule w p) :
    ‖fourierRealZeroMultiplier w v hv m C hC hb hm a‖ ≤ C*‖a‖ := by
  have he : (fourierRealZeroMultiplier w v hv m C hC hb hm a).val.val=
      weightedMultiplierCLM w v m C hC hb a.val.val := by
    apply Subtype.ext
    funext k
    exact fourierRealZeroMultiplier_apply w v hv m C hC hb hm a k
  change ‖(fourierRealZeroMultiplier w v hv m C hC hb hm a).val.val‖ ≤ C*‖a.val.val‖
  rw [he]
  exact norm_weightedMultiplier_le w v m C hC hb a.val.val

end NLS.WeightedCoeff
