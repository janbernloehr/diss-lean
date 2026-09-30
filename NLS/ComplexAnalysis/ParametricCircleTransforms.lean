import NLS.ComplexAnalysis.CircleLogarithmicPrimitive

/-!
# Jointly analytic circle transforms

The density may depend on a Banach parameter. Fixed-circle Cauchy and
logarithmic transforms are jointly analytic in the evaluation point and
that parameter. The logarithmic transform uses the same single-valued
exterior kernel as the scalar zero-period primitive.
-/

noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis
variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

def parametricCircleCauchyTransform (F : ℂ × A → ℂ) (c : ℂ) (R : ℝ) :
    ℂ × A → ℂ :=
  fun x => circleCauchyTransform (fun w => F (w,x.2)) c R x.1

def parametricCircleLogarithmicPrimitive (F : ℂ × A → ℂ) (c : ℂ) (r : ℝ) :
    ℂ × A → ℂ :=
  fun x => circleLogarithmicPrimitive (fun w => F (w,x.2)) c r x.1

/-- The Cauchy transform is jointly analytic on either side of the fixed
circle, even when the density is only specified near that circle. -/
theorem analyticOnNhd_parametricCircleCauchyTransform
    (F : ℂ × A → ℂ) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (V : Set A) (hV : IsOpen V)
    (hF : AnalyticOnNhd ℂ F (sphere c R ×ˢ V)) :
    AnalyticOnNhd ℂ (parametricCircleCauchyTransform F c R)
      ((sphere c R)ᶜ ×ˢ V) := by
  let T : ℂ × (ℂ × A) → ℂ × A := fun q => (q.1,q.2.2)
  let D : Set (ℂ × (ℂ × A)) :=
    {q | AnalyticAt ℂ F (T q) ∧ q.1 ≠ q.2.1}
  let G : ℂ × (ℂ × A) → ℂ := fun q => F (T q)/(q.1-q.2.1)
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
    exact (hq.1.comp (f := T) (analyticAt_fst.prod (ha q))).div
      (analyticAt_fst.sub (hz q)) (sub_ne_zero.mpr hq.2)
  have hcircle : ∀ x ∈ (sphere c R)ᶜ ×ˢ V, ∀ w ∈ sphere c R, (w,x) ∈ D := by
    intro x hx w hw
    exact ⟨hF (w,x.2) ⟨hw,hx.2⟩,fun he => hx.1 (he ▸ hw)⟩
  have hraw := analyticOnNhd_circleIntegral_of_jointAnalytic G hD hG c R hR
    (isClosed_sphere.isOpen_compl.prod hV) hcircle
  intro x hx
  exact analyticAt_const.mul (hraw x hx)

/-- The normalized exterior logarithm produces a joint analytic family
without choosing a logarithm branch separately for each source. -/
theorem analyticOnNhd_parametricCircleLogarithmicPrimitive
    (F : ℂ × A → ℂ) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (V : Set A) (hV : IsOpen V)
    (hF : AnalyticOnNhd ℂ F (sphere c r ×ˢ V)) :
    AnalyticOnNhd ℂ (parametricCircleLogarithmicPrimitive F c r)
      ((closedBall c r)ᶜ ×ˢ V) := by
  let T : ℂ × (ℂ × A) → ℂ × A := fun q => (q.1,q.2.2)
  let K : ℂ × (ℂ × A) → ℂ := fun q => 1-(q.1-c)/(q.2.1-c)
  let D : Set (ℂ × (ℂ × A)) :=
    {q | AnalyticAt ℂ F (T q) ∧ q.2.1 ≠ c ∧ K q ∈ slitPlane}
  let G : ℂ × (ℂ × A) → ℂ := fun q => F (T q)*log (K q)
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
    exact (hq.1.comp (f := T) (analyticAt_fst.prod (ha q))).mul
      ((analyticAt_clog hq.2.2).comp (f := K) hK)
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
  exact analyticAt_const.mul (hraw x hx)

omit [NormedAddCommGroup A] [NormedSpace ℂ A] in
/-- A zero density period makes the spectral derivative precisely the
negative inner Cauchy transform. -/
theorem hasDerivAt_parametricCircleLogarithmicPrimitive
    (F : ℂ × A → ℂ) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (a : A) (hF : AnalyticOnNhd ℂ (fun w => F (w,a)) (sphere c r))
    (hperiod : (∮ w in C(c,r), F (w,a)) = 0)
    (z : ℂ) (hz : z ∉ closedBall c r) :
    HasDerivAt (fun v => parametricCircleLogarithmicPrimitive F c r (v,a))
      (-parametricCircleCauchyTransform F c r (z,a)) z :=
  hasDerivAt_circleLogarithmicPrimitive (fun w => F (w,a)) c r hr hF hperiod z hz

end NLS.ComplexAnalysis
