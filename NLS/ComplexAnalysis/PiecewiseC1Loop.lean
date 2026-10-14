import NLS.ComplexAnalysis.ConvexHolomorphicPrimitive
import NLS.ComplexAnalysis.PrimitiveRadialContinuation
import NLS.ComplexAnalysis.AffineLoopHomotopy

/-!
# Finite piecewise C¹ contours and their actual integrals

A contour is a finite chain of C¹ paths with matching vertices and equal
initial and final vertices. Integrals are sums of the actual path integrals;
no primitive values or winding normalization enter their definition.
Corners and self-intersections are allowed. Winding is represented by the
usual normalized reciprocal-pole integral, with complex values.
-/

noncomputable section
open Set Complex
open scoped unitInterval
namespace NLS.ComplexAnalysis

/-- A finite closed chain of C¹ paths; derivatives need not match at corners. -/
structure PiecewiseC1Loop where
  count : ℕ
  vertex : ℕ → ℂ
  edge : (i : Fin count) → Path (vertex i.val) (vertex (i.val+1))
  smooth : ∀ i, ContDiffOn ℝ 1 (edge i).extend (Icc 0 1)
  closed : vertex count = vertex 0

namespace PiecewiseC1Loop

/-- All points of every piece lie in the given set. -/
def Inside (Γ : PiecewiseC1Loop) (D : Set ℂ) : Prop := ∀ i u, Γ.edge i u ∈ D

/-- Sum the actual integrals on the oriented pieces. -/
def integral (Γ : PiecewiseC1Loop) (f : ℂ → ℂ) : ℂ :=
  ∑ i : Fin Γ.count, ∫ᶜ z in Γ.edge i, holomorphicOneForm f z

/-- Normalization used for periods and winding integrals. -/
def normalizedIntegral (Γ : PiecewiseC1Loop) (f : ℂ → ℂ) : ℂ :=
  (2*Real.pi*Complex.I)⁻¹*Γ.integral f

/-- The conventional normalized reciprocal-pole integral about a point. -/
def windingIntegral (Γ : PiecewiseC1Loop) (z : ℂ) : ℂ :=
  Γ.normalizedIntegral (fun w => (w-z)⁻¹)

/-- A C¹ closed path is a one-piece contour. -/
def ofPath {a : ℂ} (γ : Path a a) (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1)) : PiecewiseC1Loop where
  count := 1
  vertex := fun _ => a
  edge := fun _ => γ
  smooth := fun _ => hγ
  closed := rfl

/-- Traverse the same smooth loop any finite number of times. -/
def repeatPath (k : ℕ) {a : ℂ} (γ : Path a a)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1)) : PiecewiseC1Loop where
  count := k
  vertex := fun _ => a
  edge := fun _ => γ
  smooth := fun _ => hγ
  closed := rfl

/-- Repeated traversal multiplies the actual integral by its count. -/
@[simp] theorem integral_repeatPath (k : ℕ) {a : ℂ} (γ : Path a a)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1)) (f : ℂ → ℂ) :
    (repeatPath k γ hγ).integral f = (k : ℂ)*(∫ᶜ z in γ, holomorphicOneForm f z) := by
  change (∑ _i : Fin k, ∫ᶜ z in γ, holomorphicOneForm f z) = _
  simp

/-- A polygonal contour, including its corners and possible repeated vertices. -/
def polygon (n : ℕ) (v : ℕ → ℂ) (hv : v n = v 0) : PiecewiseC1Loop where
  count := n
  vertex := v
  edge := fun i => Path.segment (v i.val) (v (i.val+1))
  smooth := fun _ => contDiffOn_segment_extend _ _
  closed := hv

/-- The positively oriented circle as a one-piece contour. -/
def circle (c : ℂ) (r : ℝ) : PiecewiseC1Loop :=
  ofPath (circlePath c r) ((circlePath_contDiffOn c r).of_le (by norm_num))

@[simp] theorem integral_ofPath {a : ℂ} (γ : Path a a)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1)) (f : ℂ → ℂ) :
    (ofPath γ hγ).integral f = ∫ᶜ z in γ, holomorphicOneForm f z := by
  change (∑ _i : Fin 1, ∫ᶜ z in γ, holomorphicOneForm f z) = _
  rw [Fin.sum_univ_one]

/-- Circle orientation agrees with the existing circle-integral convention. -/
@[simp] theorem integral_circle (c : ℂ) (r : ℝ) (f : ℂ → ℂ) :
    (circle c r).integral f = ∮ z in C(c,r), f z := by
  rw [circle,integral_ofPath,curveIntegral_circlePath]

/-- Every point inside a positively oriented circle has winding integral one. -/
theorem windingIntegral_circle (c z : ℂ) (r : ℝ) (hz : z ∈ Metric.ball c r) :
    (circle c r).windingIntegral z = 1 := by
  rw [windingIntegral,normalizedIntegral,integral_circle,
    circleIntegral.integral_sub_inv_of_mem_ball hz]
  exact inv_mul_cancel₀ (by simp [Real.pi_ne_zero])

/-- Scalar integrals add when the integrands are continuous on the contour's domain. -/
theorem integral_add (Γ : PiecewiseC1Loop) (f g : ℂ → ℂ) {D : Set ℂ}
    (hf : ContinuousOn f D) (hg : ContinuousOn g D) (hΓ : Γ.Inside D) :
    Γ.integral (fun z => f z+g z) = Γ.integral f+Γ.integral g := by
  have heq : holomorphicOneForm (fun z => f z+g z) = holomorphicOneForm f+holomorphicOneForm g := by
    ext z
    simp only [Pi.add_apply,add_apply,holomorphicOneForm_apply]
    ring
  have hfω : ContinuousOn (holomorphicOneForm f) D := hf.smul continuousOn_const
  have hgω : ContinuousOn (holomorphicOneForm g) D := hg.smul continuousOn_const
  unfold integral
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [heq,curveIntegral_add
    (hfω.curveIntegrable_of_contDiffOn (Γ.smooth i) (hΓ i))
    (hgω.curveIntegrable_of_contDiffOn (Γ.smooth i) (hΓ i))]

/-- Primitive differences telescope even when the individual pieces are not loops. -/
theorem integral_eq_zero_of_primitive (Γ : PiecewiseC1Loop) (f F : ℂ → ℂ)
    (D : Set ℂ) (hf : ContinuousOn f D) (hF : ∀ z ∈ D, HasDerivAt F (f z) z)
    (hΓ : Γ.Inside D) : Γ.integral f = 0 := by
  have hω : ContinuousOn (holomorphicOneForm f) D := hf.smul continuousOn_const
  have he (i : Fin Γ.count) :
      (∫ᶜ z in Γ.edge i, holomorphicOneForm f z) =
        F (Γ.vertex (i.val+1))-F (Γ.vertex i.val) :=
    curveIntegral_eq_sub_of_primitive f F D hF (Γ.edge i) (Γ.smooth i)
      (fun u hu => by simpa only [Path.extend_apply (Γ.edge i) hu] using hΓ i ⟨u,hu⟩)
      (hω.curveIntegrable_of_contDiffOn (Γ.smooth i) (hΓ i))
  simp only [integral,he]
  calc
    _ = ∑ i ∈ Finset.range Γ.count, (F (Γ.vertex (i+1))-F (Γ.vertex i)) :=
      Fin.sum_univ_eq_sum_range (fun i => F (Γ.vertex (i+1))-F (Γ.vertex i)) _
    _ = F (Γ.vertex Γ.count)-F (Γ.vertex 0) := Finset.sum_range_sub (fun i => F (Γ.vertex i)) _
    _ = 0 := by rw [Γ.closed,sub_self]

/-- Every piecewise C¹ contour in an open convex holomorphic domain has zero integral. -/
theorem integral_eq_zero_of_convex (Γ : PiecewiseC1Loop) (f : ℂ → ℂ)
    (D : Set ℂ) (hD : IsOpen D) (hc : Convex ℝ D) (hf : DifferentiableOn ℂ f D)
    (hΓ : Γ.Inside D) : Γ.integral f = 0 := by
  obtain ⟨F,hF⟩ := exists_primitive_on_convex f D hc hD hf
  exact Γ.integral_eq_zero_of_primitive f F D hf.continuousOn hF hΓ

end PiecewiseC1Loop
end NLS.ComplexAnalysis
