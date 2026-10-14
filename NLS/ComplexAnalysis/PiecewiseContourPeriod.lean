import NLS.ComplexAnalysis.PiecewiseC1Loop
import NLS.ComplexAnalysis.PrimitiveOnDiscComplement

/-!
# The period formula on a disk minus a star-convex cut

Subtract the circle period times a reciprocal pole in the cut. The
remainder has zero period and hence a primitive on the full cut disk.
Integrating along any piecewise C¹ loop leaves only its winding integral.
-/

noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis
namespace PiecewiseC1Loop

/-- Scalar multiplication commutes with the actual finite sum of path integrals. -/
theorem integral_const_mul (Γ : PiecewiseC1Loop) (a : ℂ) (f : ℂ → ℂ) :
    Γ.integral (fun z => a*f z) = a*Γ.integral f := by
  have heq : holomorphicOneForm (fun z => a*f z) = a • holomorphicOneForm f := by
    ext z
    simp only [Pi.smul_apply,smul_apply,holomorphicOneForm_apply,smul_eq_mul]
    ring
  simp only [integral,heq,curveIntegral_smul,smul_eq_mul,Finset.mul_sum]

/-- Subtract continuous integrands on the contour's domain. -/
theorem integral_sub (Γ : PiecewiseC1Loop) (f g : ℂ → ℂ) {D : Set ℂ}
    (hf : ContinuousOn f D) (hg : ContinuousOn g D) (hΓ : Γ.Inside D) :
    Γ.integral (fun z => f z-g z) = Γ.integral f-Γ.integral g := by
  have he : (fun z => f z-g z) = (fun z => f z+(-1)*g z) := by funext z; ring
  rw [he,Γ.integral_add f (fun z => (-1)*g z) hf (continuousOn_const.mul hg) hΓ,
    Γ.integral_const_mul]
  ring

/-- The integral of any piecewise C¹ loop in the whole cut disk equals
the inner circle period times its winding integral about a point of the cut. -/
theorem integral_eq_circleIntegral_mul_winding_of_starConvex_cut
    (Γ : PiecewiseC1Loop) (f : ℂ → ℂ) (d c : ℂ) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R) (K : Set ℂ) (hKclosed : IsClosed K)
    (hc : c ∈ K) (hKstar : StarConvex ℝ c K) (hKinner : K ⊆ ball d r)
    (hf : AnalyticOnNhd ℂ f (closedBall d R \ K))
    (hΓ : Γ.Inside (ball d R \ K)) :
    Γ.integral f = (∮ z in C(d,r), f z)*Γ.windingIntegral c := by
  let P : ℂ := (2*Real.pi*Complex.I)⁻¹*(∮ z in C(d,r), f z)
  let q : ℂ → ℂ := fun z => P*(z-c)⁻¹
  have hn (z : ℂ) (hz : z ∈ closedBall d R \ K) : z-c ≠ 0 := by
    intro he
    exact hz.2 (sub_eq_zero.mp he ▸ hc)
  have hq : AnalyticOnNhd ℂ q (closedBall d R \ K) :=
    fun z hz => analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).inv (hn z hz))
  have hs : sphere d r ⊆ closedBall d R \ K := by
    intro z hz
    refine ⟨closedBall_subset_closedBall hrR.le (sphere_subset_closedBall hz),?_⟩
    intro hzK
    exact (mem_ball.mp (hKinner hzK)).ne (mem_sphere.mp hz)
  have hfint : CircleIntegrable f d r := (hf.continuousOn.mono hs).circleIntegrable hr.le
  have hqint : CircleIntegrable q d r := (hq.continuousOn.mono hs).circleIntegrable hr.le
  have hpole : (∮ z in C(d,r), q z) = ∮ z in C(d,r), f z := by
    rw [show q = (fun z => P*(z-c)⁻¹) from rfl,circleIntegral.integral_const_mul,
      circleIntegral.integral_sub_inv_of_mem_ball (hKinner hc)]
    dsimp [P]
    field_simp
  have hzero : (∮ z in C(d,r), f z-q z) = 0 := by
    rw [circleIntegral.integral_sub hfint hqint,hpole,sub_self]
  obtain ⟨F,hF⟩ := exists_primitive_on_disc_complement_of_zero_period
    (fun z => f z-q z) d c r R hr hrR K hKclosed hc hKstar hKinner (hf.sub hq) hzero
  have hsub : ball d R \ K ⊆ closedBall d R \ K :=
    fun _ hz => ⟨ball_subset_closedBall hz.1,hz.2⟩
  have hprim := Γ.integral_eq_zero_of_primitive (fun z => f z-q z) F
    (ball d R \ K) ((hf.sub hq).continuousOn.mono hsub) hF hΓ
  rw [Γ.integral_sub f q (hf.continuousOn.mono hsub) (hq.continuousOn.mono hsub) hΓ] at hprim
  calc
    Γ.integral f = Γ.integral q := sub_eq_zero.mp hprim
    _ = P*Γ.integral (fun z => (z-c)⁻¹) := Γ.integral_const_mul _ _
    _ = (∮ z in C(d,r), f z)*Γ.windingIntegral c := by
      simp only [P,windingIntegral,normalizedIntegral]
      ring

end PiecewiseC1Loop
end NLS.ComplexAnalysis
