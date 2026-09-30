import NLS.ComplexAnalysis.ParametricIntervalIntegralAnalytic
import NLS.ComplexAnalysis.ConvexHolomorphicPrimitive
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Jointly analytic normalized primitives on convex charts

Integrate along the affine segment from a fixed anchor to a variable spectral
point. A fixed real interval makes this integral jointly analytic in that
point and the Banach parameter. At each source it is the unique primitive
normalized to zero at the anchor. In cosine coordinates the anchor can be
the fixed angle of a moving periodic endpoint.
-/

noncomputable section
open Set Metric Complex Filter Topology MeasureTheory
open scoped Interval
namespace NLS.ComplexAnalysis
variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

/-- The affine-segment primitive normalized at a fixed spectral anchor. -/
def parametricConvexPrimitive (F : ℂ × A → ℂ) (c : ℂ) : ℂ × A → ℂ :=
  fun x => ∫ t in (0:ℝ)..1, (x.1-c)*F (c+(t:ℂ)*(x.1-c),x.2)

omit [NormedAddCommGroup A] [NormedSpace ℂ A] in
@[simp] theorem parametricConvexPrimitive_anchor (F : ℂ × A → ℂ) (c : ℂ) (a : A) :
    parametricConvexPrimitive F c (c,a) = 0 := by
  simp [parametricConvexPrimitive]

private theorem affineSegment_mem {Ω : Set ℂ} (hconv : Convex ℝ Ω)
    {c z : ℂ} (hc : c ∈ Ω) (hz : z ∈ Ω) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    c+(t:ℂ)*(z-c) ∈ Ω := by
  have h := hconv.lineMap_mem hc hz ht
  simpa only [AffineMap.lineMap_apply_module', Complex.real_smul, add_comm] using h

/-- The normalized affine-segment primitive is jointly analytic throughout
the fixed convex spectral chart and the open parameter domain. -/
theorem analyticOnNhd_parametricConvexPrimitive
    (F : ℂ × A → ℂ) (Ω : Set ℂ) (V : Set A) (c : ℂ)
    (hΩ : IsOpen Ω) (hconv : Convex ℝ Ω) (hV : IsOpen V) (hc : c ∈ Ω)
    (hF : AnalyticOnNhd ℂ F (Ω ×ˢ V)) :
    AnalyticOnNhd ℂ (parametricConvexPrimitive F c) (Ω ×ˢ V) := by
  let T : ℂ × (ℂ × A) → ℂ × A := fun q => (c+q.1*(q.2.1-c),q.2.2)
  let D := T ⁻¹' (Ω ×ˢ V)
  let G : ℂ × (ℂ × A) → ℂ := fun q => (q.2.1-c)*F (T q)
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
    exact (hz.sub analyticAt_const).mul ((hF _ hq).comp (f := T) hTa)
  have hsegment : ∀ x ∈ Ω ×ˢ V, ∀ t ∈ uIcc (0:ℝ) 1, ((t:ℂ),x) ∈ D := by
    intro x hx t ht
    exact ⟨affineSegment_mem hconv hc hx.1 (by simpa only [uIcc_of_le zero_le_one] using ht),hx.2⟩
  exact analyticOnNhd_intervalIntegral_of_jointAnalytic G hD hG 0 1 (hΩ.prod hV) hsegment

omit [NormedAddCommGroup A] [NormedSpace ℂ A] in
/-- At a fixed source, the explicit integral equals the difference of any
primitive's endpoint values. No regularity of that primitive in the source
is required. -/
theorem parametricConvexPrimitive_eq_sub_of_primitive
    (F : ℂ × A → ℂ) (Ω : Set ℂ) (c : ℂ) (a : A)
    (hconv : Convex ℝ Ω) (hc : c ∈ Ω)
    (hF : ContinuousOn (fun z => F (z,a)) Ω)
    (P : ℂ → ℂ) (hP : ∀ z ∈ Ω, HasDerivAt P (F (z,a)) z)
    (z : ℂ) (hz : z ∈ Ω) :
    parametricConvexPrimitive F c (z,a) = P z-P c := by
  let L : ℝ → ℂ := fun t => c+(t:ℂ)*(z-c)
  have hL : Continuous L := by dsimp [L]; fun_prop
  have hLΩ (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : L t ∈ Ω :=
    affineSegment_mem hconv hc hz ht
  have hPc : ContinuousOn P Ω := fun w hw => (hP w hw).continuousAt.continuousWithinAt
  have hcont : ContinuousOn (P ∘ L) (Icc (0:ℝ) 1) :=
    hPc.comp hL.continuousOn hLΩ
  have hderiv (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
      HasDerivAt (P ∘ L) ((z-c)*F (L t,a)) t := by
    have hLc : HasDerivAt (fun w : ℂ => c+w*(z-c)) (z-c) (t:ℂ) := by
      simpa using ((hasDerivAt_id (t:ℂ)).mul_const (z-c)).const_add c
    have hLr : HasDerivAt L (z-c) t := hLc.comp_ofReal
    simpa only [Function.comp_def, smul_eq_mul, mul_comm] using
      (hP _ (hLΩ t (Ioo_subset_Icc_self ht))).scomp t hLr
  have hint : IntervalIntegrable (fun t => (z-c)*F (L t,a)) volume 0 1 :=
    (continuousOn_const.mul (hF.comp hL.continuousOn hLΩ)).intervalIntegrable_of_Icc zero_le_one
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hderiv hint
  simpa [parametricConvexPrimitive,L] using heq

/-- Each spectral slice of the explicit normalized family has exactly the
prescribed complex derivative. -/
theorem hasDerivAt_parametricConvexPrimitive
    (F : ℂ × A → ℂ) (Ω : Set ℂ) (V : Set A) (c : ℂ)
    (hΩ : IsOpen Ω) (hconv : Convex ℝ Ω) (hc : c ∈ Ω)
    (hF : AnalyticOnNhd ℂ F (Ω ×ˢ V)) (a : A) (ha : a ∈ V)
    (z : ℂ) (hz : z ∈ Ω) :
    HasDerivAt (fun w => parametricConvexPrimitive F c (w,a)) (F (z,a)) z := by
  have hFa : AnalyticOnNhd ℂ (fun w => F (w,a)) Ω := by
    intro w hw
    exact (hF (w,a) ⟨hw,ha⟩).comp (f := fun w : ℂ => (w,a))
      (analyticAt_id.prod analyticAt_const)
  obtain ⟨P,hP⟩ := exists_primitive_on_convex (fun w => F (w,a)) Ω hconv hΩ hFa.differentiableOn
  apply ((hP z hz).sub_const (P c)).congr_of_eventuallyEq
  filter_upwards [hΩ.mem_nhds hz] with w hw
  exact parametricConvexPrimitive_eq_sub_of_primitive F Ω c a hconv hc hFa.continuousOn P hP w hw

/-- Evaluating the normalized family at an analytic moving spectral point
preserves source analyticity. -/
theorem analyticAt_parametricConvexPrimitive_moving_terminal
    (F : ℂ × A → ℂ) (Ω : Set ℂ) (V : Set A) (c : ℂ)
    (hΩ : IsOpen Ω) (hconv : Convex ℝ Ω) (hV : IsOpen V) (hc : c ∈ Ω)
    (hF : AnalyticOnNhd ℂ F (Ω ×ˢ V)) (μ : A → ℂ) (a : A)
    (ha : a ∈ V) (hμ : AnalyticAt ℂ μ a) (hμΩ : μ a ∈ Ω) :
    AnalyticAt ℂ (fun b => parametricConvexPrimitive F c (μ b,b)) a :=
  (analyticOnNhd_parametricConvexPrimitive F Ω V c hΩ hconv hV hc hF (μ a,a) ⟨hμΩ,ha⟩).comp
    (f := fun b => (μ b,b)) (hμ.prod analyticAt_id)

end NLS.ComplexAnalysis
