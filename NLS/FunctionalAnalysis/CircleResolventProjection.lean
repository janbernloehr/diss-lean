import NLS.FunctionalAnalysis.CircleIntegrationMap
import NLS.ComplexAnalysis.CircleOpenCollar
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Operator-valued circular resolvent projections

A resolvent is integrated in the norm of its Banach algebra. Two nested
circles give the projection product identity using the resolvent identity
and Fubini. No scalar characteristic determinant is assumed.
-/
noncomputable section
open Complex Metric Set Filter Topology
namespace NLS.CircleIntegral
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

omit [CompleteSpace A] in
/-- Operator-norm circle integration preserves continuous dependence on an arbitrary parameter. -/
theorem continuousOn_parametric_circleIntegral {X : Type*} [TopologicalSpace X]
    (f : X → ℂ → A) (s : Set X) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hf : ContinuousOn (Function.uncurry f) (s ×ˢ sphere c r)) :
    ContinuousOn (fun x => ∮ z in C(c,r), f x z) s := by
  let : NormedSpace ℝ A := NormedSpace.restrictScalars ℝ ℂ A
  have hc : Continuous (fun p : s × ℝ => f p.1.val (circleMap c r p.2)) :=
    hf.comp_continuous ((continuous_subtype_val.comp continuous_fst).prodMk
      ((continuous_circleMap c r).comp continuous_snd))
      (fun p => ⟨p.1.property,circleMap_mem_sphere c hr p.2⟩)
  have hd : Continuous (fun p : s × ℝ => deriv (circleMap c r) p.2) := by
    simp only [deriv_circleMap]
    fun_prop
  have ht := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := MeasureTheory.volume)
    (f := fun (x : s) (θ : ℝ) => deriv (circleMap c r) θ • f x.val (circleMap c r θ))
    (hd.smul hc) 0 (2*Real.pi)
  exact continuousOn_iff_continuous_domRestrict.mpr ht

/-- The normalized operator-norm circle integral. -/
def normalized (F : ℂ → A) (c : ℂ) (r : ℝ) : A :=
  (2*Real.pi*I:ℂ)⁻¹ • ∮ z in C(c,r), F z

omit [CompleteSpace A] in
/-- The normalized operator integral depends continuously on parameters. -/
theorem continuousOn_normalized {X : Type*} [TopologicalSpace X]
    (f : X → ℂ → A) (s : Set X) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hf : ContinuousOn (Function.uncurry f) (s ×ˢ sphere c r)) :
    ContinuousOn (fun x => normalized (f x) c r) s :=
  continuousOn_const.smul (continuousOn_parametric_circleIntegral f s c r hr hf)

/-- Multiplication by a fixed algebra element commutes with circle integration. -/
theorem integral_mul_const (F : ℂ → A) (b : A) (c : ℂ) (r : ℝ)
    (hF : CircleIntegrable F c r) :
    (∮ z in C(c,r), F z)*b = ∮ z in C(c,r), F z*b :=
  map ((ContinuousLinearMap.mul ℂ A).flip b) hF

/-- Left multiplication also commutes with circle integration. -/
theorem integral_const_mul (a : A) (F : ℂ → A) (c : ℂ) (r : ℝ)
    (hF : CircleIntegrable F c r) :
    a*(∮ z in C(c,r), F z) = ∮ z in C(c,r), a*F z :=
  map (ContinuousLinearMap.mul ℂ A a) hF

/-- The inverse Cauchy kernel has zero integral when its pole is outside the closed disk. -/
theorem integral_inv_sub_eq_zero {c w : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hw : w ∉ closedBall c r) : (∮ z in C(c,r), (w-z)⁻¹) = 0 := by
  apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr countable_empty
  · exact (continuousOn_const.sub continuousOn_id).inv₀ (fun z hz =>
      sub_ne_zero.mpr (ne_of_mem_of_not_mem hz hw).symm)
  · intro z hz
    exact (differentiableAt_const w |>.sub differentiableAt_id).inv
      (sub_ne_zero.mpr (ne_of_mem_of_not_mem (ball_subset_closedBall hz.1) hw).symm)

/-- The Cauchy kernel also integrates to zero with the usual z-minus-pole orientation. -/
theorem integral_sub_inv_eq_zero {c w : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hw : w ∉ closedBall c r) : (∮ z in C(c,r), (z-w)⁻¹) = 0 := by
  apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr countable_empty
  · exact (continuousOn_id.sub continuousOn_const).inv₀ (fun z hz =>
      sub_ne_zero.mpr (ne_of_mem_of_not_mem hz hw))
  · intro z hz
    exact (differentiableAt_id.sub_const w).inv
      (sub_ne_zero.mpr (ne_of_mem_of_not_mem (ball_subset_closedBall hz.1) hw))

/-- The algebra-valued product formula on nested circles for a genuine resolvent identity.
The convention is F(z)=(z-L)^(-1), hence F(z)-F(w)=(w-z)F(z)F(w). -/
theorem integral_resolvent_mul_nested (F : ℂ → A) (c : ℂ) (r R : ℝ)
    (hr : 0 ≤ r) (hrR : r < R)
    (hFr : ContinuousOn F (sphere c r)) (hFR : ContinuousOn F (sphere c R))
    (hres : ∀ z ∈ sphere c r, ∀ w ∈ sphere c R,
      F z-F w = (w-z) • (F z*F w)) :
    (∮ z in C(c,r), F z)*(∮ w in C(c,R), F w) =
      (2*Real.pi*I:ℂ) • ∮ z in C(c,r), F z := by
  have hR : 0 ≤ R := hr.trans hrR.le
  have hne (z : ℂ) (hz : z ∈ sphere c r) (w : ℂ) (hw : w ∈ sphere c R) : w-z ≠ 0 := by
    intro he
    have hwz := sub_eq_zero.mp he
    have hzr := mem_sphere.mp hz
    have hwR := mem_sphere.mp hw
    rw [hwz] at hwR
    linarith
  let S := sphere c r ×ˢ sphere c R
  have hk : ContinuousOn (fun p : ℂ × ℂ => (p.2-p.1)⁻¹) S :=
    (continuous_snd.sub continuous_fst).continuousOn.inv₀
      (fun p hp => hne p.1 hp.1 p.2 hp.2)
  let f : ℂ → ℂ → A := fun z w => (w-z)⁻¹ • F z
  let g : ℂ → ℂ → A := fun z w => (w-z)⁻¹ • F w
  have hf : ContinuousOn (Function.uncurry f) S := hk.smul
    (hFr.comp continuous_fst.continuousOn (fun _ h => h.1))
  have hg : ContinuousOn (Function.uncurry g) S := hk.smul
    (hFR.comp continuous_snd.continuousOn (fun _ h => h.2))
  have heq (z : ℂ) (hz : z ∈ sphere c r) (w : ℂ) (hw : w ∈ sphere c R) :
      F z*F w = f z w-g z w := by
    dsimp [f,g]
    rw [← smul_sub,hres z hz w hw,smul_smul,inv_mul_cancel₀ (hne z hz w hw),one_smul]
  have hint_f (z : ℂ) (hz : z ∈ sphere c r) : CircleIntegrable (f z) c R :=
    (hf.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hw => ⟨hz,hw⟩)).circleIntegrable hR
  have hint_g (z : ℂ) (hz : z ∈ sphere c r) : CircleIntegrable (g z) c R :=
    (hg.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hw => ⟨hz,hw⟩)).circleIntegrable hR
  have hfval (z : ℂ) (hz : z ∈ sphere c r) :
      (∮ w in C(c,R), f z w) = (2*Real.pi*I:ℂ) • F z := by
    rw [show f z = fun w => (w-z)⁻¹ • F z from rfl,
      circleIntegral.integral_smul_const,circleIntegral.integral_sub_inv_of_mem_ball]
    exact (mem_sphere.mp hz).trans_lt hrR
  have hgval (w : ℂ) (hw : w ∈ sphere c R) : (∮ z in C(c,r), g z w) = 0 := by
    rw [show (fun z => g z w) = fun z => (w-z)⁻¹ • F w from rfl,
      circleIntegral.integral_smul_const,integral_inv_sub_eq_zero hr,zero_smul]
    simpa only [mem_closedBall,mem_sphere.mp hw] using not_le.mpr hrR
  have hmain : (∮ z in C(c,r), ∮ w in C(c,R), F z*F w) =
      (∮ z in C(c,r), ∮ w in C(c,R), f z w) -
        ∮ z in C(c,r), ∮ w in C(c,R), g z w := by
    have hcf := continuousOn_parametric_circleIntegral f (sphere c r) c R hR hf
    have hcg := continuousOn_parametric_circleIntegral g (sphere c r) c R hR hg
    rw [← circleIntegral.integral_sub (hcf.circleIntegrable hr) (hcg.circleIntegrable hr)]
    apply circleIntegral.integral_congr hr
    intro z hz
    dsimp only
    rw [← circleIntegral.integral_sub (hint_f z hz) (hint_g z hz)]
    exact circleIntegral.integral_congr hR (fun w hw => heq z hz w hw)
  rw [integral_mul_const _ _ _ _ (hFr.circleIntegrable hr)]
  conv_lhs => arg 1; ext z; rw [integral_const_mul _ _ _ _ (hFR.circleIntegrable hR)]
  rw [hmain]
  have hfint : (∮ z in C(c,r), ∮ w in C(c,R), f z w) =
      (2*Real.pi*I:ℂ) • ∮ z in C(c,r), F z := by
    rw [← circleIntegral.integral_smul]
    exact circleIntegral.integral_congr hr hfval
  rw [hfint,swap hr hR hg]
  have hzero : (∮ w in C(c,R), ∮ z in C(c,r), g z w) = 0 := by
    calc
      _ = ∮ w in C(c,R), (0:A) := circleIntegral.integral_congr hR hgval
      _ = 0 := by simp [circleIntegral]
  rw [hzero,sub_zero]

/-- Normalization turns the nested resolvent integral product into the inner integral. -/
theorem normalized_resolvent_mul_nested (F : ℂ → A) (c : ℂ) (r R : ℝ)
    (hr : 0 ≤ r) (hrR : r < R)
    (hFr : ContinuousOn F (sphere c r)) (hFR : ContinuousOn F (sphere c R))
    (hres : ∀ z ∈ sphere c r, ∀ w ∈ sphere c R,
      F z-F w = (w-z) • (F z*F w)) :
    normalized F c r*normalized F c R = normalized F c r := by
  unfold normalized
  rw [smul_mul_assoc,mul_smul_comm,integral_resolvent_mul_nested F c r R hr hrR hFr hFR hres]
  simp only [smul_smul]
  congr 1
  have hκ : (2*Real.pi*I:ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  field_simp

omit [CompleteSpace A] in
/-- The operator-valued circle integral is unchanged across a holomorphic annulus. -/
theorem normalized_eq_of_annulus (F : ℂ → A) (c : ℂ) (r R : ℝ)
    (hr : 0 < r) (hrR : r ≤ R)
    (hc : ContinuousOn F (closedBall c R \ ball c r))
    (hd : ∀ z ∈ ball c R \ closedBall c r, DifferentiableAt ℂ F z) :
    normalized F c R = normalized F c r := by
  have he := Complex.circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable
    hr hrR countable_empty
    ((continuousOn_id.sub continuousOn_const).smul hc)
    (fun z hz => (differentiableAt_id.sub_const c).smul (hd z hz.1))
  have hcongr (s : ℝ) (hs : 0 < s) :
      (∮ z in C(c,s), (z-c)⁻¹ • ((z-c) • F z)) = ∮ z in C(c,s), F z := by
    apply circleIntegral.integral_congr hs.le
    intro z hz
    have hzc : z-c ≠ 0 := by
      intro h
      have heq := sub_eq_zero.mp h
      have hh := mem_sphere.mp hz
      rw [heq,dist_self] at hh
      linarith
    change (z-c)⁻¹ • ((z-c) • F z) = F z
    rw [smul_smul,inv_mul_cancel₀ hzc,one_smul]
  change (∮ z in C(c,R), (z-c)⁻¹ • ((z-c) • F z)) =
    ∮ z in C(c,r), (z-c)⁻¹ • ((z-c) • F z) at he
  rw [hcongr R (hr.trans_le hrR),hcongr r hr] at he
  exact congrArg (fun x : A => (2*Real.pi*I:ℂ)⁻¹ • x) he

/-- Integrating a genuine resolvent around a circle gives an idempotent operator.
Only a holomorphic collar outside that circle is required. -/
theorem isIdempotentElem_normalized_resolvent (F : ℂ → A) (c : ℂ) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R)
    (hc : ContinuousOn F (closedBall c R \ ball c r))
    (hd : ∀ z ∈ ball c R \ closedBall c r, DifferentiableAt ℂ F z)
    (hres : ∀ z ∈ sphere c r, ∀ w ∈ sphere c R,
      F z-F w = (w-z) • (F z*F w)) : IsIdempotentElem (normalized F c r) := by
  have hFr : ContinuousOn F (sphere c r) := hc.mono (by
    intro z hz
    exact ⟨(mem_sphere.mp hz).le.trans hrR.le,not_lt.mpr (mem_sphere.mp hz).ge⟩)
  have hFR : ContinuousOn F (sphere c R) := hc.mono (by
    intro z hz
    exact ⟨(mem_sphere.mp hz).le,not_lt.mpr (hrR.le.trans (mem_sphere.mp hz).ge)⟩)
  have he := normalized_resolvent_mul_nested F c r R hr.le hrR hFr hFR hres
  rw [normalized_eq_of_annulus F c r R hr hrR.le hc hd] at he
  exact he

/-- A circle in an open holomorphic resolvent region defines an actual idempotent. -/
theorem isIdempotentElem_normalized_resolvent_of_open (F : ℂ → A)
    (U : Set ℂ) (hU : IsOpen U) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hcircle : sphere c r ⊆ U) (hF : ∀ z ∈ U, AnalyticAt ℂ F z)
    (hres : ∀ z ∈ U, ∀ w ∈ U, F z-F w = (w-z) • (F z*F w)) :
    IsIdempotentElem (normalized F c r) := by
  obtain ⟨R,hrR,hann⟩ := exists_closedAnnulus_subset_of_sphere_subset_open c r hU hcircle
  apply isIdempotentElem_normalized_resolvent F c r R hr hrR
  · exact fun z hz => (hF z (hann hz)).continuousAt.continuousWithinAt
  · intro z hz
    exact (hF z (hann ⟨(show dist z c ≤ R from le_of_lt hz.1),fun h => hz.2 (ball_subset_closedBall h)⟩)).differentiableAt
  · intro z hz w hw
    exact hres z (hcircle hz) w (hann ⟨(mem_sphere.mp hw).le,
      not_lt.mpr (hrR.le.trans (mem_sphere.mp hw).ge)⟩)

section Compact
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- An operator-norm circle integral of compact operators is compact. -/
theorem isCompactOperator_integral {F : ℂ → E →L[ℂ] E} {c : ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hc : ContinuousOn F (sphere c r))
    (hcompact : ∀ z ∈ sphere c r, IsCompactOperator (F z)) :
    IsCompactOperator (∮ z in C(c,r), F z : E →L[ℂ] E) := by
  classical
  let K := compactOperator (RingHom.id ℂ) E E
  have hclosed : IsClosed (K : Set (E →L[ℂ] E)) := isClosed_setOfPred_isCompactOperator
  let : CompleteSpace K := hclosed.completeSpace_coe
  let g : ℂ → K := fun z => if hz : z ∈ sphere c r then ⟨F z,hcompact z hz⟩ else 0
  have hg (z : ℂ) (hz : z ∈ sphere c r) : (g z : E →L[ℂ] E) = F z := by
    simp only [g,dif_pos hz]
  have hgc : ContinuousOn g (sphere c r) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have ht : Continuous (fun z : sphere c r => (⟨F z.val,hcompact z.val z.property⟩ : K)) :=
      (hc.comp_continuous continuous_subtype_val (fun z => z.property)).subtype_mk _
    exact ht.congr (fun z => by
      change (⟨F z.val,hcompact z.val z.property⟩ : K) = g z.val
      simp only [g,dif_pos z.property])
  have he := map K.subtypeL (hgc.circleIntegrable hr)
  have he' : K.subtypeL (∮ z in C(c,r), g z) = ∮ z in C(c,r), F z :=
    he.trans (circleIntegral.integral_congr hr hg)
  have hp : IsCompactOperator (K.subtypeL (∮ z in C(c,r), g z)) :=
    (∮ z in C(c,r), g z).property
  rwa [he'] at hp

/-- The circular Riesz operator of a compact resolvent is compact. -/
theorem isCompactOperator_normalized {F : ℂ → E →L[ℂ] E} {c : ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hc : ContinuousOn F (sphere c r))
    (hcompact : ∀ z ∈ sphere c r, IsCompactOperator (F z)) :
    IsCompactOperator (normalized F c r : E →L[ℂ] E) :=
  (isCompactOperator_integral hr hc hcompact).smul _

omit [CompleteSpace E] in
/-- Every compact bounded idempotent has finite-dimensional range. -/
theorem finiteDimensional_range_of_compact_idempotent (P : E →L[ℂ] E)
    (hP : IsIdempotentElem P) (hcompact : IsCompactOperator P) :
    FiniteDimensional ℂ P.range := by
  have hfix (x : E) : x ∈ P.range ↔ P x = x := by
    constructor
    · rintro ⟨y,rfl⟩
      exact congrArg (fun T : E →L[ℂ] E => T y) hP
    · intro hx
      exact ⟨x,hx⟩
  have hclosed : IsClosed (P.range : Set E) := by
    have he : (P.range : Set E) = {x | P x = x} := Set.ext hfix
    rw [he]
    exact isClosed_eq P.continuous continuous_id
  have hmaps : MapsTo P P.range P.range := fun x _ => ⟨x,rfl⟩
  have hr := hcompact.restrict hmaps hclosed
  have he : (P.toLinearMap.restrict hmaps : P.range → P.range) = id := by
    funext x
    exact Subtype.ext ((hfix x.val).mp x.property)
  rw [he] at hr
  exact FiniteDimensional.of_isCompactOperator_id hr

end Compact
end NLS.CircleIntegral
