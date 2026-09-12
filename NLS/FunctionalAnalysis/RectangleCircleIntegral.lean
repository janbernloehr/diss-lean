import NLS.FunctionalAnalysis.RectangleIntegral
import NLS.FunctionalAnalysis.CircleIntegral
import Mathlib.Topology.Order.ProjIcc
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Interchanging rectangular and circular integrals

Fubini's theorem applies to continuous Banach-valued integrands on the product
of the two compact contours. No continuity or analyticity is required in the
regions bounded by the contours.
-/

noncomputable section
open Complex Metric Set MeasureTheory
namespace NLS.RectangleIntegral
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A continuous family of edge integrals is integrable around the parameter circle. -/
theorem circleIntegrable_intervalIntegral {f : ℝ → ℂ → E} {a b : ℝ} {c : ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hf : ContinuousOn (Function.uncurry f) (uIcc a b ×ˢ sphere c r)) :
    CircleIntegrable (fun ζ => ∫ t : ℝ in a..b, f t ζ) c r := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  let g : ℝ → ℝ → E := fun θ t => f (projIcc (min a b) (max a b) min_le_max t) (circleMap c r θ)
  have hg : Continuous (Function.uncurry g) := by
    apply hf.comp_continuous
      (((continuous_subtype_val.comp (continuous_projIcc (h := (min_le_max : min a b ≤ max a b)))).comp continuous_snd).prodMk
        ((continuous_circleMap c r).comp continuous_fst))
    intro t
    exact ⟨(projIcc _ _ min_le_max t.2).property, by simp [abs_of_nonneg hr]⟩
  have hcont := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume) hg a b
  have he : (fun θ => ∫ t : ℝ in a..b, g θ t) = fun θ => ∫ t : ℝ in a..b, f t (circleMap c r θ) := by
    funext θ
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp [g]
    rw [projIcc_of_mem (h := (min_le_max : min a b ≤ max a b)) ht]
  rw [he] at hcont
  exact hcont.intervalIntegrable _ _

/-- Fubini interchanges a real edge integral and a circular integral. -/
theorem interval_circle_swap {f : ℝ → ℂ → E} {a b : ℝ} {c : ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hf : ContinuousOn (Function.uncurry f) (uIcc a b ×ˢ sphere c r)) :
    (∫ t : ℝ in a..b, ∮ ζ in C(c, r), f t ζ) =
      ∮ ζ in C(c, r), ∫ t : ℝ in a..b, f t ζ := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  let g : ℝ → ℝ → E := fun t θ => deriv (circleMap c r) θ • f t (circleMap c r θ)
  have hfg : ContinuousOn (fun t : ℝ × ℝ => f t.1 (circleMap c r t.2))
      (uIcc a b ×ˢ uIcc 0 (2 * Real.pi)) := by
    exact hf.comp (continuous_fst.prodMk ((continuous_circleMap c r).comp continuous_snd)).continuousOn
      (fun t ht => ⟨ht.1, by simp [abs_of_nonneg hr]⟩)
  have hg : ContinuousOn (Function.uncurry g) (uIcc a b ×ˢ uIcc 0 (2 * Real.pi)) := by
    have hd : Continuous (fun t : ℝ × ℝ => deriv (circleMap c r) t.2) := by
      simp only [deriv_circleMap]; fun_prop
    exact hd.continuousOn.smul hfg
  have hi : IntegrableOn (Function.uncurry g) (uIoc a b ×ˢ uIoc 0 (2 * Real.pi)) :=
    (hg.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
      (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  have hs := MeasureTheory.intervalIntegral_intervalIntegral_swap hi
  simpa only [circleIntegral, g, ← intervalIntegral.integral_smul] using hs

/-- Continuous integrands on the product of a rectangular boundary and a circle satisfy Fubini. -/
theorem circle_swap {f : ℂ → ℂ → E} {z w c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hf : ContinuousOn (Function.uncurry f) (boundary z w ×ˢ sphere c r)) :
    integral (fun ζ => ∮ η in C(c, r), f ζ η) z w =
      ∮ η in C(c, r), integral (fun ζ => f ζ η) z w := by
  have hh (y : ℝ) (hy : y = z.im ∨ y = w.im) :
      ContinuousOn (Function.uncurry (fun x : ℝ => f (x + y * I))) (uIcc z.re w.re ×ˢ sphere c r) :=
    hf.comp (((Complex.continuous_ofReal.comp continuous_fst).add continuous_const).prodMk continuous_snd).continuousOn
      (fun t ht => ⟨horizontal_mem z w ht.1 hy, ht.2⟩)
  have hv (x : ℝ) (hx : x = z.re ∨ x = w.re) :
      ContinuousOn (Function.uncurry (fun y : ℝ => f (x + y * I))) (uIcc z.im w.im ×ˢ sphere c r) :=
    hf.comp ((continuous_const.add ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const)).prodMk
      continuous_snd).continuousOn (fun t ht => ⟨vertical_mem z w ht.1 hx, ht.2⟩)
  have hb := circleIntegrable_intervalIntegral hr (hh _ (Or.inl rfl))
  have ht := circleIntegrable_intervalIntegral hr (hh _ (Or.inr rfl))
  have hright := circleIntegrable_intervalIntegral hr (hv _ (Or.inr rfl))
  have hleft := circleIntegrable_intervalIntegral hr (hv _ (Or.inl rfl))
  have hir : CircleIntegrable (fun η => I • ∫ t : ℝ in z.im..w.im, f (w.re + t * I) η) c r := hright.smul I
  have hil : CircleIntegrable (fun η => I • ∫ t : ℝ in z.im..w.im, f (z.re + t * I) η) c r := hleft.smul I
  have hbt : CircleIntegrable (fun η => (∫ t : ℝ in z.re..w.re, f (t + z.im * I) η) -
      ∫ t : ℝ in z.re..w.re, f (t + w.im * I) η) c r := hb.sub ht
  have hsum : CircleIntegrable (fun η => ((∫ t : ℝ in z.re..w.re, f (t + z.im * I) η) -
      ∫ t : ℝ in z.re..w.re, f (t + w.im * I) η) + I • ∫ t : ℝ in z.im..w.im, f (w.re + t * I) η) c r := hbt.add hir
  simp only [integral]
  rw [circleIntegral.integral_sub hsum hil,
    circleIntegral.integral_add hbt hir, circleIntegral.integral_sub hb ht,
    circleIntegral.integral_smul, circleIntegral.integral_smul,
    interval_circle_swap hr (hh _ (Or.inl rfl)), interval_circle_swap hr (hh _ (Or.inr rfl)),
    interval_circle_swap hr (hv _ (Or.inr rfl)), interval_circle_swap hr (hv _ (Or.inl rfl))]

end NLS.RectangleIntegral
