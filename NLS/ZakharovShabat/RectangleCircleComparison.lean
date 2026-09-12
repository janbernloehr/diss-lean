import NLS.ZakharovShabat.RectangleRootSelection
import NLS.FunctionalAnalysis.RectangleCircleIntegral

/-!
# Comparison of rectangular contours with enclosing circles

The resolvent identity and mixed-contour Fubini show that multiplying the
rectangular contour operator by an enclosing circular projection leaves it
unchanged on the entire base space. This controls all vectors, including the
complement of the finite spectral clusters.
-/

noncomputable section
open Complex Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem rectangle_integral_mul_resolvent_outer (hp : p ≠ ⊤) (φ : PairSpace p) (z w a : ℂ)
    (hc : RectangleIntegral.boundary z w ⊆ resolventSet hp φ) (ha : a ∈ resolventSet hp φ)
    (hao : a ∉ uIcc z.re w.re ×ℂ uIcc z.im w.im) :
    RectangleIntegral.integral (fun ζ => resolvent hp φ ζ * resolvent hp φ a) z w =
      RectangleIntegral.integral (fun ζ => (a - ζ)⁻¹ • resolvent hp φ ζ) z w := by
  have hne (ζ : ℂ) (hζ : ζ ∈ RectangleIntegral.boundary z w) : a ≠ ζ :=
    fun h => hao (h ▸ RectangleIntegral.boundary_subset_rectangle z w hζ)
  have hinv : ContinuousOn (fun ζ : ℂ => (a - ζ)⁻¹) (RectangleIntegral.boundary z w) :=
    (continuousOn_const.sub continuousOn_id).inv₀ fun ζ hζ => by
      change a - ζ ≠ 0
      exact sub_ne_zero.mpr (hne ζ hζ)
  have hi1 : RectangleIntegral.Integrable (fun ζ => (a - ζ)⁻¹ • resolvent hp φ ζ) z w :=
    RectangleIntegral.integrable_of_continuousOn (hinv.smul ((analyticOnNhd_resolvent hp φ).continuousOn.mono hc))
  have hi2 : RectangleIntegral.Integrable (fun ζ => (a - ζ)⁻¹ • resolvent hp φ a) z w :=
    RectangleIntegral.integrable_of_continuousOn (hinv.smul continuousOn_const)
  have heq : RectangleIntegral.integral (fun ζ => resolvent hp φ ζ * resolvent hp φ a) z w =
      RectangleIntegral.integral (fun ζ => (a - ζ)⁻¹ • resolvent hp φ ζ -
        (a - ζ)⁻¹ • resolvent hp φ a) z w := by
    apply RectangleIntegral.congr
    intro ζ hζ
    dsimp only
    calc
      _ = (a - ζ)⁻¹ • ((a - ζ) • (resolvent hp φ ζ * resolvent hp φ a)) :=
        (inv_smul_smul₀ (sub_ne_zero.mpr (hne ζ hζ)) _).symm
      _ = (a - ζ)⁻¹ • (resolvent hp φ ζ - resolvent hp φ a) :=
        congrArg (fun A : PairSpace p →L[ℂ] PairSpace p => (a - ζ)⁻¹ • A)
          (resolvent_identity hp φ ζ a (hc hζ) ha).symm
      _ = _ := smul_sub _ _ _
  have hi0 : RectangleIntegral.integral (fun ζ : ℂ => (a - ζ)⁻¹) z w = 0 := by
    have he : (fun ζ : ℂ => (a - ζ)⁻¹) = fun ζ => (-1 : ℂ) • (ζ - a)⁻¹ := by
      funext ζ
      rw [show a - ζ = -(ζ - a) by abel, inv_neg, neg_one_smul]
    rw [he, RectangleIntegral.integral_smul, RectangleIntegral.integral_inv_sub_of_notMem hao, smul_zero]
  rw [heq, RectangleIntegral.integral_sub hi1 hi2, RectangleIntegral.integral_smul_const,
    hi0, zero_smul, sub_zero]

/-- An enclosing circular projection captures the entire action of a rectangular contour operator. -/
theorem resolventRectangleIntegral_mul_enclosing_circle (hp : p ≠ ⊤) (φ : PairSpace p)
    (z w c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : RectangleIntegral.boundary z w ⊆ resolventSet hp φ)
    (hC : sphere c r ⊆ resolventSet hp φ)
    (hbox : uIcc z.re w.re ×ℂ uIcc z.im w.im ⊆ ball c r) :
    resolventRectangleIntegral hp φ z w * resolventCircleIntegral hp φ c r =
      resolventRectangleIntegral hp φ z w := by
  let S := resolvent hp φ
  let Q := RectangleIntegral.integral S z w
  let P := ∮ η in C(c, r), S η
  have hiQ : RectangleIntegral.Integrable S z w := rectangleIntegrable_resolvent hp φ z w hc
  have hiP : CircleIntegrable S c r := circleIntegrable_resolvent hp φ c r hr hC
  have houter (η : ℂ) (hη : η ∈ sphere c r) : η ∉ uIcc z.re w.re ×ℂ uIcc z.im w.im :=
    fun h => sphere_disjoint_ball.le_bot ⟨hη, hbox h⟩
  have hneq (t : ℂ × ℂ) (ht : t ∈ RectangleIntegral.boundary z w ×ˢ sphere c r) : t.2 ≠ t.1 :=
    fun h => houter t.2 ht.2 (h ▸ RectangleIntegral.boundary_subset_rectangle z w ht.1)
  have hM : ContinuousOn (fun t : ℂ × ℂ => (t.2 - t.1)⁻¹ • S t.1)
      (RectangleIntegral.boundary z w ×ˢ sphere c r) := by
    have hinv : ContinuousOn (fun t : ℂ × ℂ => (t.2 - t.1)⁻¹)
        (RectangleIntegral.boundary z w ×ˢ sphere c r) :=
      (continuousOn_snd.sub continuousOn_fst).inv₀ (fun t ht => sub_ne_zero.mpr (hneq t ht))
    exact hinv.smul (((analyticOnNhd_resolvent hp φ).continuousOn.mono hc).comp
      continuousOn_fst (fun _ ht => ht.1))
  have hraw : Q * P = (2 * Real.pi * I : ℂ) • Q := by
    calc
      Q * P = ∮ η in C(c, r), Q * S η :=
        NLS.CircleIntegral.map (ContinuousLinearMap.mul ℂ _ Q) hiP
      _ = ∮ η in C(c, r), RectangleIntegral.integral (fun ζ => S ζ * S η) z w := by
        apply circleIntegral.integral_congr hr
        intro η _
        exact RectangleIntegral.map ((ContinuousLinearMap.mul ℂ _).flip (S η)) hiQ
      _ = ∮ η in C(c, r), RectangleIntegral.integral (fun ζ => (η - ζ)⁻¹ • S ζ) z w := by
        apply circleIntegral.integral_congr hr
        intro η hη
        exact rectangle_integral_mul_resolvent_outer hp φ z w η hc (hC hη) (houter η hη)
      _ = RectangleIntegral.integral (fun ζ => ∮ η in C(c, r), (η - ζ)⁻¹ • S ζ) z w :=
        (RectangleIntegral.circle_swap hr hM).symm
      _ = RectangleIntegral.integral (fun ζ => (2 * Real.pi * I : ℂ) • S ζ) z w := by
        apply RectangleIntegral.congr
        intro ζ hζ
        dsimp only
        rw [circleIntegral.integral_smul_const,
          circleIntegral.integral_sub_inv_of_mem_ball (hbox (RectangleIntegral.boundary_subset_rectangle z w hζ))]
      _ = _ := RectangleIntegral.integral_smul _ _ _ _
  change ((2 * Real.pi * I : ℂ)⁻¹ • Q) * ((2 * Real.pi * I : ℂ)⁻¹ • P) =
    (2 * Real.pi * I : ℂ)⁻¹ • Q
  rw [smul_mul_assoc, mul_smul_comm, hraw]
  simp [smul_smul, mul_assoc, Real.pi_ne_zero]

end NLS.ZakharovShabat
