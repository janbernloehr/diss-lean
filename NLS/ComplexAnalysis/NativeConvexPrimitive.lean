import NLS.ComplexAnalysis.ParametricConvexPrimitive
import Mathlib.Analysis.Normed.Module.DoubleDual

/-!
# Banach-valued normalized segment primitives

The integral is taken in the target Banach space. Joint analyticity is
proved before using continuous linear functionals to identify its derivative.
-/

noncomputable section
open Set Metric Complex Filter Topology MeasureTheory
open scoped Interval
namespace NLS.ComplexAnalysis
variable {A B : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]
  [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]

omit [CompleteSpace B] in
/-- A strongly analytic function has the prescribed derivative if all its
bounded complex-linear scalar observations have that derivative. -/
theorem hasDerivAt_of_analyticAt_of_dual (F : ℂ → B) (z : ℂ) (v : B)
    (hF : AnalyticAt ℂ F z)
    (h : ∀ L : B →L[ℂ] ℂ, HasDerivAt (fun w => L (F w)) (L v) z) :
    HasDerivAt F v z := by
  have hd := hF.differentiableAt.hasDerivAt
  have heq : deriv F z = v := by
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
    intro L
    exact (L.hasFDerivAt.comp_hasDerivAt z hd).unique (h L)
  exact heq ▸ hd

def nativeConvexPrimitive (F : ℂ × A → B) (c : ℂ) : ℂ × A → B :=
  fun x => ∫ t in (0:ℝ)..1, (x.1-c) • F (c+(t:ℂ)*(x.1-c),x.2)

omit [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace B] in
@[simp] theorem nativeConvexPrimitive_anchor (F : ℂ × A → B) (c : ℂ) (a : A) :
    nativeConvexPrimitive F c (c,a) = 0 := by
  simp [nativeConvexPrimitive]

private theorem native_affineSegment_mem {Ω : Set ℂ} (hconv : Convex ℝ Ω)
    {c z : ℂ} (hc : c ∈ Ω) (hz : z ∈ Ω) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    c+(t:ℂ)*(z-c) ∈ Ω := by
  have h := hconv.lineMap_mem hc hz ht
  simpa only [AffineMap.lineMap_apply_module', Complex.real_smul, add_comm] using h

theorem analyticOnNhd_nativeConvexPrimitive
    (F : ℂ × A → B) (Ω : Set ℂ) (V : Set A) (c : ℂ)
    (hΩ : IsOpen Ω) (hconv : Convex ℝ Ω) (hV : IsOpen V) (hc : c ∈ Ω)
    (hF : AnalyticOnNhd ℂ F (Ω ×ˢ V)) :
    AnalyticOnNhd ℂ (nativeConvexPrimitive F c) (Ω ×ˢ V) := by
  let T : ℂ × (ℂ × A) → ℂ × A := fun q => (c+q.1*(q.2.1-c),q.2.2)
  let D := T ⁻¹' (Ω ×ˢ V)
  let G : ℂ × (ℂ × A) → B := fun q => (q.2.1-c) • F (T q)
  have hT : Continuous T := by dsimp [T]; fun_prop
  have hD : IsOpen D := (hΩ.prod hV).preimage hT
  have hG : AnalyticOnNhd ℂ G D := by
    intro q hq
    have hz : AnalyticAt ℂ (fun q : ℂ × (ℂ × A) => q.2.1) q :=
      analyticAt_fst.comp (f := fun q : ℂ × (ℂ × A) => q.2) analyticAt_snd
    have ha : AnalyticAt ℂ (fun q : ℂ × (ℂ × A) => q.2.2) q :=
      analyticAt_snd.comp (f := fun q : ℂ × (ℂ × A) => q.2) analyticAt_snd
    have hTa : AnalyticAt ℂ T q :=
      (analyticAt_const.add (analyticAt_fst.mul (hz.sub analyticAt_const))).prod ha
    exact (hz.sub analyticAt_const).smul ((hF _ hq).comp (f := T) hTa)
  have hsegment : ∀ x ∈ Ω ×ˢ V, ∀ t ∈ uIcc (0:ℝ) 1, ((t:ℂ),x) ∈ D := by
    intro x hx t ht
    exact ⟨native_affineSegment_mem hconv hc hx.1
      (by simpa only [uIcc_of_le zero_le_one] using ht),hx.2⟩
  exact analyticOnNhd_intervalIntegral_of_jointAnalytic G hD hG 0 1 (hΩ.prod hV) hsegment

omit [NormedAddCommGroup A] [NormedSpace ℂ A] in
/-- Scalar observation commutes with the genuine vector integral. -/
theorem map_nativeConvexPrimitive
    (L : B →L[ℂ] ℂ) (F : ℂ × A → B) (Ω : Set ℂ) (c : ℂ)
    (hconv : Convex ℝ Ω) (hc : c ∈ Ω) (a : A)
    (hF : ContinuousOn (fun z => F (z,a)) Ω) (z : ℂ) (hz : z ∈ Ω) :
    L (nativeConvexPrimitive F c (z,a)) =
      parametricConvexPrimitive (fun x => L (F x)) c (z,a) := by
  let : NormedSpace ℝ B := NormedSpace.restrictScalars ℝ ℂ B
  have hi : IntervalIntegrable (fun t : ℝ => (z-c) • F (c+(t:ℂ)*(z-c),a)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
    apply continuousOn_const.smul
    apply hF.comp (by fun_prop)
    intro t ht
    exact native_affineSegment_mem hconv hc hz ht
  unfold nativeConvexPrimitive
  rw [← L.intervalIntegral_comp_comm hi]
  simp only [parametricConvexPrimitive, map_smul, smul_eq_mul]

theorem hasDerivAt_nativeConvexPrimitive
    (F : ℂ × A → B) (Ω : Set ℂ) (V : Set A) (c : ℂ)
    (hΩ : IsOpen Ω) (hconv : Convex ℝ Ω) (hV : IsOpen V) (hc : c ∈ Ω)
    (hF : AnalyticOnNhd ℂ F (Ω ×ˢ V)) (a : A) (ha : a ∈ V)
    (z : ℂ) (hz : z ∈ Ω) :
    HasDerivAt (fun w => nativeConvexPrimitive F c (w,a)) (F (z,a)) z := by
  have hslice : AnalyticOnNhd ℂ (fun w => F (w,a)) Ω := by
    intro w hw
    exact (hF (w,a) ⟨hw,ha⟩).comp (f := fun w : ℂ => (w,a))
      (analyticAt_id.prod analyticAt_const)
  apply hasDerivAt_of_analyticAt_of_dual
  · exact (analyticOnNhd_nativeConvexPrimitive F Ω V c hΩ hconv hV hc hF (z,a)
      ⟨hz,ha⟩).comp (f := fun w : ℂ => (w,a)) (analyticAt_id.prod analyticAt_const)
  · intro L
    have hLF : AnalyticOnNhd ℂ (fun x => L (F x)) (Ω ×ˢ V) :=
      fun x hx => (L.analyticAt (F x)).comp (hF x hx)
    apply (hasDerivAt_parametricConvexPrimitive _ Ω V c hΩ hconv hc hLF a ha z hz
      ).congr_of_eventuallyEq
    filter_upwards [hΩ.mem_nhds hz] with w hw
    exact map_nativeConvexPrimitive L F Ω c hconv hc a hslice.continuousOn w hw

end NLS.ComplexAnalysis
