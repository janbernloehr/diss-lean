import NLS.ComplexAnalysis.ParametricCircleTransforms
import NLS.ComplexAnalysis.NativeConvexPrimitive

/-!
# Native Banach-valued circle transforms

The density may depend on a Banach parameter. Fixed-circle Cauchy and
logarithmic transforms are jointly analytic in the evaluation point and
that parameter. The logarithmic transform uses the same single-valued
exterior kernel as the scalar zero-period primitive.
-/

noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis
variable {A B : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]
  [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]

def nativeCircleCauchyTransform (F : ℂ × A → B) (c : ℂ) (R : ℝ) :
    ℂ × A → B :=
  fun x => (2*Real.pi*I : ℂ)⁻¹ • ∮ w in C(c,R), (w-x.1)⁻¹ • F (w,x.2)

def nativeCircleLogarithmicPrimitive (F : ℂ × A → B) (c : ℂ) (r : ℝ) :
    ℂ × A → B :=
  fun x => (2*Real.pi*I : ℂ)⁻¹ • ∮ w in C(c,r), log (1-(w-c)/(x.1-c)) • F (w,x.2)

/-- The Cauchy transform is jointly analytic on either side of the fixed
circle, even when the density is only specified near that circle. -/
theorem analyticOnNhd_nativeCircleCauchyTransform
    (F : ℂ × A → B) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (V : Set A) (hV : IsOpen V)
    (hF : AnalyticOnNhd ℂ F (sphere c R ×ˢ V)) :
    AnalyticOnNhd ℂ (nativeCircleCauchyTransform F c R)
      ((sphere c R)ᶜ ×ˢ V) := by
  let T : ℂ × (ℂ × A) → ℂ × A := fun q => (q.1,q.2.2)
  let D : Set (ℂ × (ℂ × A)) :=
    {q | AnalyticAt ℂ F (T q) ∧ q.1 ≠ q.2.1}
  let G : ℂ × (ℂ × A) → B := fun q => (q.1-q.2.1)⁻¹ • F (T q)
  have hT : Continuous T := by dsimp [T]; fun_prop
  have hz : ∀ q : ℂ × (ℂ × A), AnalyticAt ℂ (fun q : ℂ × (ℂ × A) => q.2.1) q :=
    fun _ => analyticAt_fst.comp (f := fun q : ℂ × (ℂ × A) => q.2) analyticAt_snd
  have ha : ∀ q : ℂ × (ℂ × A), AnalyticAt ℂ (fun q : ℂ × (ℂ × A) => q.2.2) q :=
    fun _ => analyticAt_snd.comp (f := fun q : ℂ × (ℂ × A) => q.2) analyticAt_snd
  have hD : IsOpen D :=
    ((isOpen_analyticAt ℂ F).preimage hT).inter
      (isOpen_ne_fun continuous_fst (continuous_fst.comp continuous_snd))
  have hG : AnalyticOnNhd ℂ G D := by
    intro q hq
    exact ((analyticAt_fst.sub (hz q)).inv (sub_ne_zero.mpr hq.2)).smul
      (hq.1.comp (f := T) (analyticAt_fst.prod (ha q)))
  have hcircle : ∀ x ∈ (sphere c R)ᶜ ×ˢ V, ∀ w ∈ sphere c R, (w,x) ∈ D := by
    intro x hx w hw
    exact ⟨hF (w,x.2) ⟨hw,hx.2⟩,fun he => hx.1 (he ▸ hw)⟩
  have hraw := analyticOnNhd_circleIntegral_of_jointAnalytic G hD hG c R hR
    (isClosed_sphere.isOpen_compl.prod hV) hcircle
  intro x hx
  exact analyticAt_const.smul (hraw x hx)

/-- The normalized exterior logarithm produces a joint analytic family
without choosing a logarithm branch separately for each source. -/
theorem analyticOnNhd_nativeCircleLogarithmicPrimitive
    (F : ℂ × A → B) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (V : Set A) (hV : IsOpen V)
    (hF : AnalyticOnNhd ℂ F (sphere c r ×ˢ V)) :
    AnalyticOnNhd ℂ (nativeCircleLogarithmicPrimitive F c r)
      ((closedBall c r)ᶜ ×ˢ V) := by
  let T : ℂ × (ℂ × A) → ℂ × A := fun q => (q.1,q.2.2)
  let K : ℂ × (ℂ × A) → ℂ := fun q => 1-(q.1-c)/(q.2.1-c)
  let D : Set (ℂ × (ℂ × A)) :=
    {q | AnalyticAt ℂ F (T q) ∧ q.2.1 ≠ c ∧ K q ∈ slitPlane}
  let G : ℂ × (ℂ × A) → B := fun q => log (K q) • F (T q)
  have hT : Continuous T := by dsimp [T]; fun_prop
  have hz : ∀ q : ℂ × (ℂ × A), AnalyticAt ℂ (fun q : ℂ × (ℂ × A) => q.2.1) q :=
    fun _ => analyticAt_fst.comp (f := fun q : ℂ × (ℂ × A) => q.2) analyticAt_snd
  have ha : ∀ q : ℂ × (ℂ × A), AnalyticAt ℂ (fun q : ℂ × (ℂ × A) => q.2.2) q :=
    fun _ => analyticAt_snd.comp (f := fun q : ℂ × (ℂ × A) => q.2) analyticAt_snd
  have hD : IsOpen D := by
    have hne : IsOpen {q : ℂ × (ℂ × A) | q.2.1 ≠ c} :=
      isOpen_ne_fun (continuous_fst.comp continuous_snd) continuous_const
    have hK : ContinuousOn K {q | q.2.1 ≠ c} :=
      continuousOn_const.sub ((continuousOn_fst.sub continuousOn_const).div
        ((continuous_fst.comp continuous_snd).continuousOn.sub continuousOn_const)
        (fun q hq => sub_ne_zero.mpr hq))
    exact ((isOpen_analyticAt ℂ F).preimage hT).inter
      (hK.isOpen_inter_preimage hne isOpen_slitPlane)
  have hG : AnalyticOnNhd ℂ G D := by
    intro q hq
    have hK : AnalyticAt ℂ K q := analyticAt_const.sub
      ((analyticAt_fst.sub analyticAt_const).div ((hz q).sub analyticAt_const)
        (sub_ne_zero.mpr hq.2.1))
    exact ((analyticAt_clog hq.2.2).comp (f := K) hK).smul
      (hq.1.comp (f := T) (analyticAt_fst.prod (ha q)))
  have hcircle : ∀ x ∈ (closedBall c r)ᶜ ×ˢ V, ∀ w ∈ sphere c r, (w,x) ∈ D := by
    intro x hx w hw
    have hzn : r < ‖x.1-c‖ := by
      simpa only [mem_compl_iff,mem_closedBall,not_le,dist_eq_norm] using hx.1
    exact ⟨hF (w,x.2) ⟨hw,hx.2⟩,
      sub_ne_zero.mp (norm_pos_iff.mp (lt_of_le_of_lt hr hzn)),
      circleLogKernel_mem_slitPlane c w x.1 r hr hw hx.1⟩
  have hraw := analyticOnNhd_circleIntegral_of_jointAnalytic G hD hG c r hr
    (isClosed_closedBall.isOpen_compl.prod hV) hcircle
  intro x hx
  exact analyticAt_const.smul (hraw x hx)

omit [NormedAddCommGroup A] [NormedSpace ℂ A] in
/-- Bounded scalar observations commute with Cauchy projection. -/
theorem map_nativeCircleCauchyTransform (L : B →L[ℂ] ℂ) (F : ℂ × A → B)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R) (a : A)
    (hF : ContinuousOn (fun w => F (w,a)) (sphere c R))
    (z : ℂ) (hz : z ∉ sphere c R) :
    L (nativeCircleCauchyTransform F c R (z,a)) =
      parametricCircleCauchyTransform (fun x => L (F x)) c R (z,a) := by
  have hi : CircleIntegrable (fun w => (w-z)⁻¹ • F (w,a)) c R :=
    ((show ContinuousOn (fun w : ℂ => (w-z)⁻¹) (sphere c R) from
      (continuousOn_id.sub continuousOn_const).inv₀
      (fun w hw => sub_ne_zero.mpr (fun he => by
        change w = z at he
        exact hz (he ▸ hw)))).smul hF).circleIntegrable hR
  rw [nativeCircleCauchyTransform, map_smul, NLS.CircleIntegral.map L hi]
  simp only [parametricCircleCauchyTransform, circleCauchyTransform, map_smul,
    smul_eq_mul, div_eq_mul_inv, mul_comm]

omit [NormedAddCommGroup A] [NormedSpace ℂ A] in
/-- The exterior logarithm commutes with bounded scalar observation. -/
theorem map_nativeCircleLogarithmicPrimitive (L : B →L[ℂ] ℂ) (F : ℂ × A → B)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (a : A)
    (hF : ContinuousOn (fun w => F (w,a)) (sphere c r))
    (z : ℂ) (hz : z ∉ closedBall c r) :
    L (nativeCircleLogarithmicPrimitive F c r (z,a)) =
      parametricCircleLogarithmicPrimitive (fun x => L (F x)) c r (z,a) := by
  have hkernel : ContinuousOn (fun w => log (1-(w-c)/(z-c))) (sphere c r) := by
    apply ContinuousOn.clog
    · exact continuousOn_const.sub ((continuousOn_id.sub continuousOn_const).div_const _)
    · intro w hw
      exact circleLogKernel_mem_slitPlane c w z r hr hw hz
  have hi : CircleIntegrable (fun w => log (1-(w-c)/(z-c)) • F (w,a)) c r :=
    (hkernel.smul hF).circleIntegrable hr
  rw [nativeCircleLogarithmicPrimitive, map_smul, NLS.CircleIntegral.map L hi]
  simp only [parametricCircleLogarithmicPrimitive, circleLogarithmicPrimitive,
    map_smul, smul_eq_mul, mul_comm]

/-- The zero vector period cancels the logarithm's extra constant term. -/
theorem hasDerivAt_nativeCircleLogarithmicPrimitive
    (F : ℂ × A → B) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (V : Set A) (hV : IsOpen V)
    (hF : AnalyticOnNhd ℂ F (sphere c r ×ˢ V))
    (a : A) (ha : a ∈ V) (hperiod : (∮ w in C(c,r), F (w,a)) = 0)
    (z : ℂ) (hz : z ∉ closedBall c r) :
    HasDerivAt (fun v => nativeCircleLogarithmicPrimitive F c r (v,a))
      (-nativeCircleCauchyTransform F c r (z,a)) z := by
  have hslice : AnalyticOnNhd ℂ (fun w => F (w,a)) (sphere c r) := by
    intro w hw
    exact (hF (w,a) ⟨hw,ha⟩).comp (f := fun w : ℂ => (w,a))
      (analyticAt_id.prod analyticAt_const)
  apply hasDerivAt_of_analyticAt_of_dual
  · exact (analyticOnNhd_nativeCircleLogarithmicPrimitive F c r hr V hV hF (z,a)
      ⟨hz,ha⟩).comp (f := fun w : ℂ => (w,a)) (analyticAt_id.prod analyticAt_const)
  · intro L
    have hLF : AnalyticOnNhd ℂ (fun w => L (F (w,a))) (sphere c r) :=
      fun w hw => (L.analyticAt (F (w,a))).comp (f := fun w : ℂ => F (w,a)) (hslice w hw)
    have hp : (∮ w in C(c,r), L (F (w,a))) = 0 := by
      rw [← NLS.CircleIntegral.map L (hslice.continuousOn.circleIntegrable hr), hperiod, map_zero]
    have hd := hasDerivAt_parametricCircleLogarithmicPrimitive (fun x => L (F x))
      c r hr a hLF hp z hz
    rw [map_neg, map_nativeCircleCauchyTransform L F c r hr a hslice.continuousOn z
      (fun hs => hz (sphere_subset_closedBall hs))]
    apply hd.congr_of_eventuallyEq
    filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hz] with w hw
    exact map_nativeCircleLogarithmicPrimitive L F c r hr a hslice.continuousOn w hw

omit [NormedAddCommGroup A] [NormedSpace ℂ A] in
/-- Cauchy's annular decomposition holds as an equality in the target space. -/
theorem nativeCircleCauchyTransform_outer_sub_inner
    (F : ℂ × A → B) (c : ℂ) (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R)
    (a : A) (hF : AnalyticOnNhd ℂ (fun w => F (w,a)) (closedBall c R \ ball c r))
    (z : ℂ) (hz : z ∈ ball c R \ closedBall c r) :
    nativeCircleCauchyTransform F c R (z,a) -
      nativeCircleCauchyTransform F c r (z,a) = F (z,a) := by
  have houter : sphere c R ⊆ closedBall c R \ ball c r := by
    intro w hw
    refine ⟨sphere_subset_closedBall hw,?_⟩
    intro h
    have h1 := mem_sphere.mp hw
    have h2 := mem_ball.mp h
    linarith
  have hinner : sphere c r ⊆ closedBall c R \ ball c r := by
    intro w hw
    exact ⟨mem_closedBall.mpr ((mem_sphere.mp hw).le.trans hrR),
      fun h => sphere_disjoint_ball.le_bot ⟨hw,h⟩⟩
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
  intro L
  rw [map_sub, map_nativeCircleCauchyTransform L F c R (hr.le.trans hrR) a
    (hF.continuousOn.mono houter) z
    (fun hs => sphere_disjoint_ball.le_bot ⟨hs,hz.1⟩),
    map_nativeCircleCauchyTransform L F c r hr.le a
    (hF.continuousOn.mono hinner) z (fun hs => hz.2 (sphere_subset_closedBall hs))]
  exact circleCauchyTransform_outer_sub_inner (fun w => L (F (w,a))) c r R hr hrR
    (fun w hw => (L.analyticAt (F (w,a))).comp (f := fun w : ℂ => F (w,a)) (hF w hw)) z hz

end NLS.ComplexAnalysis
