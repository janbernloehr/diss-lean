import NLS.KdV.HillHminusOneHighContourAction
import NLS.KdV.HillHminusOneBoundaryAction
import NLS.ComplexAnalysis.EndpointPrimitivePeriod

/-! # Actual high Hill contour actions equal their real-gap boundary integral

The contour has proved winding one, the integrand is the original actual
discriminant derivative divided by the constructed physical root, and
integration by parts and the ellipse period give the two-over-pi gap
formula. This is local high-gap identification, not global action gluing.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex MeasureTheory NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

theorem exists_hillHminus_contour_eq_gap_boundary_action
    (n : ℕ+) (r epsilon : ℝ) (hr : 0 < r) (hepsilon : epsilon < 1)
    (V : Set PeriodOneHminusOne) (K : ℂ × PeriodOneHminusOne → ℂ)
    (hJ : AnalyticOnNhd ℂ (hillHminusJointNormalizedGapRoot n r K)
      (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) ×ˢ V))
    (q : PeriodOneHminusOne) (hqV : q ∈ V) (l u : ℝ) (hlu : l < u)
    (hpair : HillHminusHighGapPair q n r (l : ℂ) (u : ℂ))
    (hf : ∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
      K (z,q) = -hillHminusGapPolynomial n r (z,q)*hillHminusJointNormalizedGapRoot n r K (z,q)^2 /
        (4*((Real.pi : ℂ)*(n : ℕ))^2))
    (hnorm : ∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
      ‖hillHminusJointNormalizedGapRoot n r K (z,q)-1‖ ≤ epsilon)
    (htrace : ∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
      squaredCosh (K (z,q)) = (-1 : ℂ)^(n : ℕ)*hillHminusDiscriminant q z/2) :
    ∃ R : ℝ, 1 < R ∧ ∀ rho : ℝ, ∀ hrho : 1 < rho, rho ≤ R →
      let Γ := standardRootEllipseLoop (((l+u)/2 : ℝ) : ℂ) (((u-l)/2 : ℝ) : ℂ) rho (by linarith)
      Γ.Inside (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) \ segment ℝ (l : ℂ) (u : ℂ)) ∧
      Γ.windingIntegral (((l+u)/2 : ℝ) : ℂ) = 1 ∧
      hillHminusHighContourAction n r K q (l : ℂ) (u : ℂ) Γ = hillHminusGapBoundaryAction K q l u := by
  let U : Set ℂ := ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r)
  let t : ℂ := (((l+u)/2 : ℝ) : ℂ)
  let d : ℂ := (((u-l)/2 : ℝ) : ℂ)
  let c : ℂ := (Real.pi : ℂ)*(n : ℕ)
  let S : ℂ → ℂ := fun z => hillHminusJointNormalizedGapRoot n r K (z,q)
  have hS : AnalyticOnNhd ℂ S U := by
    intro z hz
    exact (hJ (z,q) ⟨hz,hqV⟩).comp (f := fun w : ℂ => (w,q)) (analyticAt_id.prod analyticAt_const)
  have hd : d ≠ 0 := by dsimp [d]; exact_mod_cast (by linarith : (u-l)/2 ≠ 0)
  have hm : ((l : ℂ)+(u : ℂ))/2 = t := by dsimp [t]; push_cast; rfl
  have hgap : ((u : ℂ)-(l : ℂ))^2 = (2*d)^2 := by dsimp [d]; push_cast; ring
  have hseg : standardRootGapSegment t d = segment ℝ (l : ℂ) (u : ℂ) := by
    rw [standardRootGapSegment_eq_segment]
    have hl : t-d = (l : ℂ) := by dsimp [t,d]; push_cast; ring
    have hu : t+d = (u : ℂ) := by dsimp [t,d]; push_cast; ring
    rw [hl,hu]
  have hgapU : standardRootGapSegment t d ⊆ U := by
    rw [hseg]
    exact (convex_ball _ _).segment_subset hpair.left_mem hpair.right_mem
  obtain ⟨R,hR,hperiod⟩ := exists_endpointPrimitive_ellipse_period c t d hd U isOpen_ball hgapU S hS
  have hFn : hillHminusOffGapPrimitive n r K q (l : ℂ) (u : ℂ) =
      (fun z => I/(2*c)*normalizedStandardRoot t ((2*d)^2) z*S z) := by
    funext z
    dsimp only [hillHminusOffGapPrimitive]
    rw [hm,hgap]
  obtain ⟨_,hA,_⟩ := hillHminusGapBoundaryAction_properties n r epsilon hr hepsilon V K hJ
    q hqV l u hlu.le hpair hf hnorm
  have hmean : (∫ θ in (0 : ℝ)..Real.pi,
      (Real.sin θ : ℂ)^2*hillHminusJointNormalizedGapRoot n r K
        (((((l+u)/2+(u-l)/2*Real.cos θ : ℝ) : ℂ)),q)) =
      ∫ θ in (0 : ℝ)..Real.pi, (Real.sin θ : ℂ)^2*S (t+d*(Real.cos θ : ℂ)) := by
    congr 1
    funext θ
    dsimp [t,d,S]
    push_cast
    rfl
  dsimp only [normalizedSemicircleMean] at hA
  rw [hmean] at hA
  have hA' : hillHminusGapBoundaryAction K q l u = d^2/((Real.pi : ℂ)*c)*
      (∫ θ in (0 : ℝ)..Real.pi, (Real.sin θ : ℂ)^2*S (t+d*(Real.cos θ : ℂ))) := by
    rw [hA]
    dsimp [d,c]
    push_cast
    ring
  refine ⟨R,hR,?_⟩
  intro rho hrho hrhoR
  obtain ⟨hin,hw,he⟩ := hperiod rho hrho hrhoR
  rw [hseg] at hin
  refine ⟨hin,hw,?_⟩
  rw [hillHminusHighContourAction_eq_neg_primitive_period n r hr K q (l : ℂ) (u : ℂ) hpair hS hf htrace _ hin,
    hFn,he,hA']
  ring

end NLS.KdV
