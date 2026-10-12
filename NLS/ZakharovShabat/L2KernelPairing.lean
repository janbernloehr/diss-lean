import NLS.ZakharovShabat.L2VariationEquation

/-! # The adjugate forcing integral in the physical L2 topology

Products of solution coordinates are continuous test functions. The
bounded scalar Volterra map integrates them against a rough L2 direction.
-/
noncomputable section
open Set Complex MeasureTheory
open NLS.LinearVolterra
namespace NLS.ZakharovShabat

private def firstCurve : Curve (ℂ × ℂ) →L[ℂ] Curve ℂ :=
  ContinuousLinearMap.compLeftContinuous ℂ _ (ContinuousLinearMap.fst ℂ ℂ ℂ)
private def secondCurve : Curve (ℂ × ℂ) →L[ℂ] Curve ℂ :=
  ContinuousLinearMap.compLeftContinuous ℂ _ (ContinuousLinearMap.snd ℂ ℂ ℂ)

/-- One row of the adjugate applied to the potential forcing, integrated in time. -/
def l2KernelPairing (h : IntervalPairL2) (w y : Curve (ℂ × ℂ)) : Curve ℂ :=
  I • (l2ScalarVolterraCLM h.fst (secondCurve w*secondCurve y)+
    l2ScalarVolterraCLM h.snd (firstCurve w*firstCurve y))

theorem continuous_l2KernelPairing :
    Continuous (fun p : IntervalPairL2 × (Curve (ℂ × ℂ) × Curve (ℂ × ℂ)) =>
      l2KernelPairing p.1 p.2.1 p.2.2) := by
  have hh := (WithLp.prodContinuousLinearEquiv 2 ℂ IntervalL2 IntervalL2).continuous.comp
    (continuous_fst : Continuous (fun p : IntervalPairL2 × (Curve (ℂ × ℂ) × Curve (ℂ × ℂ)) => p.1))
  have hw₁ : Continuous (fun p : IntervalPairL2 × (Curve (ℂ × ℂ) × Curve (ℂ × ℂ)) =>
      firstCurve p.2.1) := firstCurve.continuous.comp continuous_snd.fst
  have hw₂ : Continuous (fun p : IntervalPairL2 × (Curve (ℂ × ℂ) × Curve (ℂ × ℂ)) =>
      secondCurve p.2.1) := secondCurve.continuous.comp continuous_snd.fst
  have hy₁ : Continuous (fun p : IntervalPairL2 × (Curve (ℂ × ℂ) × Curve (ℂ × ℂ)) =>
      firstCurve p.2.2) := firstCurve.continuous.comp continuous_snd.snd
  have hy₂ : Continuous (fun p : IntervalPairL2 × (Curve (ℂ × ℂ) × Curve (ℂ × ℂ)) =>
      secondCurve p.2.2) := secondCurve.continuous.comp continuous_snd.snd
  exact (((l2ScalarVolterraCLM.continuous.comp hh.fst).clm_apply (hw₂.mul hy₂)).add
    ((l2ScalarVolterraCLM.continuous.comp hh.snd).clm_apply (hw₁.mul hy₁))).const_smul I

theorem l2KernelPairing_sub (h : IntervalPairL2) (w₁ w₂ y : Curve (ℂ × ℂ)) :
    l2KernelPairing h (w₁-w₂) y = l2KernelPairing h w₁ y-l2KernelPairing h w₂ y := by
  apply ContinuousMap.ext
  intro t
  simp only [l2KernelPairing,map_sub,sub_mul]
  change I*((_ - _)+(_ - _)) = I*(_+_)-I*(_+_)
  ring

theorem l2KernelPairing_smul (h : IntervalPairL2) (c : ℂ) (w y : Curve (ℂ × ℂ)) :
    l2KernelPairing h (c • w) y = c • l2KernelPairing h w y := by
  apply ContinuousMap.ext
  intro t
  simp only [l2KernelPairing,map_smul,smul_mul_assoc]
  change I*(c*_+c*_) = c*(I*(_+_))
  ring

/-- This is the ordinary, unconjugated integral of the original L2 representatives. -/
theorem l2KernelPairing_apply (h : IntervalPairL2) (w y : Curve (ℂ × ℂ))
    (t : Icc (0 : ℝ) 1) :
    l2KernelPairing h w y t = ∫ s in (0 : ℝ)..t.val,
      I*(h.ofLp.1 s*(extend w s).2*(extend y s).2+
         h.ofLp.2 s*(extend w s).1*(extend y s).1) := by
  have h₁ := intervalIntegrable_intervalL2_mul h.fst
    (curveBoundedExtension ℂ (secondCurve w*secondCurve y)) t
  have h₂ := intervalIntegrable_intervalL2_mul h.snd
    (curveBoundedExtension ℂ (firstCurve w*firstCurve y)) t
  change IntervalIntegrable (fun s => h.ofLp.1 s*((extend w s).2*(extend y s).2)) volume 0 t.val at h₁
  change IntervalIntegrable (fun s => h.ofLp.2 s*((extend w s).1*(extend y s).1)) volume 0 t.val at h₂
  simp only [l2KernelPairing,ContinuousMap.smul_apply,ContinuousMap.add_apply,
    l2ScalarVolterraCLM_apply,l2ScalarVolterra_apply,smul_eq_mul]
  change I*((∫ s in (0 : ℝ)..t.val, h.ofLp.1 s*((extend w s).2*(extend y s).2))+
    (∫ s in (0 : ℝ)..t.val, h.ofLp.2 s*((extend w s).1*(extend y s).1))) = _
  rw [← intervalIntegral.integral_add h₁ h₂,← intervalIntegral.integral_const_mul]
  congr 1
  funext s
  ring

/-- Continuous directions recover the literal classical integrand on every subinterval. -/
theorem l2KernelPairing_of_continuous (H w y : Curve (ℂ × ℂ))
    (t : Icc (0 : ℝ) 1) :
    l2KernelPairing (continuousPotentialL2Class H) w y t = ∫ s in (0 : ℝ)..t.val,
      I*((extend H s).1*(extend w s).2*(extend y s).2+
         (extend H s).2*(extend w s).1*(extend y s).1) := by
  rw [l2KernelPairing_apply]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le t.property.1]
  filter_upwards [ae_mono (Measure.restrict_mono (Ioc_subset_Ioc_right t.property.2) (le_refl volume))
    (continuousPotentialL2Class_representative H)] with s hs
  have h₁ := congrArg Prod.fst hs
  have h₂ := congrArg Prod.snd hs
  change (continuousPotentialL2Class H).ofLp.1 s = (extend H s).1 at h₁
  change (continuousPotentialL2Class H).ofLp.2 s = (extend H s).2 at h₂
  rw [h₁,h₂]

/-- Continuity of the actual variation in both parameters and the perturbation. -/
theorem continuous_l2VariationCurve (v : ℂ × ℂ) :
    Continuous (fun p : (ℂ × IntervalPairL2) × (ℂ × IntervalPairL2) =>
      l2VariationCurve p.1 p.2 v) := by
  have hs : Continuous (fun p : (ℂ × IntervalPairL2) × (ℂ × IntervalPairL2) =>
      l2SolutionOperator p.1) := continuous_l2SolutionOperator.comp continuous_fst
  have hk : Continuous (fun p : (ℂ × IntervalPairL2) × (ℂ × IntervalPairL2) =>
      l2Volterra p.2) := by
    convert! l2VolterraCoefficientMap.continuous.comp continuous_snd
  have hu : Continuous (fun p : (ℂ × IntervalPairL2) × (ℂ × IntervalPairL2) =>
      l2SolutionCurve p.1.2 p.1.1 v) := (continuous_l2SolutionCurve_joint v).comp continuous_fst
  exact hs.clm_apply (hk.clm_apply hu)

end NLS.ZakharovShabat
