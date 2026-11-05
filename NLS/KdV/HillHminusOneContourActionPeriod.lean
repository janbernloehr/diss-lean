import NLS.KdV.HillHminusOneHighContourAction
import NLS.ComplexAnalysis.EndpointPrimitiveCircuitPeriod

/-! # Exact native high Hill actions for arbitrary contour winding

The endpoints may be complex or coincident. Every actual contour in the
original open gap complement has the same semicircle formula, multiplied
by its actual winding. This proves contour independence and complex gap
normalization without dividing by the gap square.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

theorem hillHminusHighContourAction_circuit_formula
    (n : ℕ+) (r : ℝ) (hr : 0 < r) (K : ℂ × PeriodOneHminusOne → ℂ)
    (q : PeriodOneHminusOne) (l u : ℂ) (hpair : HillHminusHighGapPair q n r l u)
    (hS : AnalyticOnNhd ℂ (fun z => hillHminusJointNormalizedGapRoot n r K (z,q))
      (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r)))
    (hf : ∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
      K (z,q) = -hillHminusGapPolynomial n r (z,q)*hillHminusJointNormalizedGapRoot n r K (z,q)^2 /
        (4*((Real.pi : ℂ)*(n : ℕ))^2))
    (htrace : ∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
      squaredCosh (K (z,q)) = (-1 : ℂ)^(n : ℕ)*hillHminusDiscriminant q z/2)
    (Γ : PiecewiseC1Loop)
    (hΓ : Γ.Inside (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) \ segment ℝ l u)) :
    hillHminusHighContourAction n r K q l u Γ =
      ((u-l)^2/(8*((Real.pi : ℂ)*(n : ℕ))))*
        normalizedSemicircleMean (fun a : ℝ => hillHminusJointNormalizedGapRoot n r K
          ((l+u)/2+(u-l)/2*(a : ℂ),q))*Γ.windingIntegral ((l+u)/2) := by
  let t : ℂ := (l+u)/2
  let d : ℂ := (u-l)/2
  let c : ℂ := (Real.pi : ℂ)*(n : ℕ)
  let S : ℂ → ℂ := fun z => hillHminusJointNormalizedGapRoot n r K (z,q)
  have hseg : standardRootGapSegment t d = segment ℝ l u := by
    rw [standardRootGapSegment_eq_segment]
    congr 1 <;> dsimp [t,d] <;> ring
  have hgap : standardRootGapSegment t d ⊆
      ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) := by
    rw [hseg]
    exact (convex_ball _ _).segment_subset hpair.left_mem hpair.right_mem
  have hΓ' : Γ.Inside (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) \ standardRootGapSegment t d) := by
    rwa [hseg]
  have hF : hillHminusOffGapPrimitive n r K q l u =
      (fun z => I/(2*c)*normalizedStandardRoot t ((2*d)^2) z*S z) := by
    funext z
    dsimp only [hillHminusOffGapPrimitive,t,c,S]
    have hd : (u-l)^2 = (2*d)^2 := by dsimp [d]; ring
    rw [hd]
  rw [hillHminusHighContourAction_eq_neg_primitive_period n r hr K q l u hpair hS hf htrace Γ hΓ,hF,
    endpointPrimitive_circuit_period c t d _ _ hgap S hS Γ hΓ']
  dsimp [normalizedSemicircleMean,t,d,c,S]
  ring

theorem norm_hillHminusHighContourAction_error_le
    (n : ℕ+) (r epsilon : ℝ) (hr : 0 < r) (K : ℂ × PeriodOneHminusOne → ℂ)
    (q : PeriodOneHminusOne) (l u : ℂ) (hpair : HillHminusHighGapPair q n r l u)
    (hS : AnalyticOnNhd ℂ (fun z => hillHminusJointNormalizedGapRoot n r K (z,q))
      (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r)))
    (hf : ∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
      K (z,q) = -hillHminusGapPolynomial n r (z,q)*hillHminusJointNormalizedGapRoot n r K (z,q)^2 /
        (4*((Real.pi : ℂ)*(n : ℕ))^2))
    (htrace : ∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
      squaredCosh (K (z,q)) = (-1 : ℂ)^(n : ℕ)*hillHminusDiscriminant q z/2)
    (hnorm : ∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
      ‖hillHminusJointNormalizedGapRoot n r K (z,q)-1‖ ≤ epsilon)
    (Γ : PiecewiseC1Loop)
    (hΓ : Γ.Inside (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) \ segment ℝ l u))
    (hw : Γ.windingIntegral ((l+u)/2) = 1) :
    ‖(8*((Real.pi : ℂ)*(n : ℕ)))*hillHminusHighContourAction n r K q l u Γ-(u-l)^2‖ ≤
      ‖u-l‖^2*epsilon := by
  let f : ℝ → ℂ := fun a => hillHminusJointNormalizedGapRoot n r K ((l+u)/2+(u-l)/2*(a : ℂ),q)
  have hmap (a : ℝ) (ha : a ∈ Icc (-1) 1) :
      (l+u)/2+(u-l)/2*(a : ℂ) ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) := by
    have hs : (l+u)/2+(u-l)/2*(a : ℂ) ∈ standardRootGapSegment ((l+u)/2) ((u-l)/2) := ⟨a,ha,rfl⟩
    rw [standardRootGapSegment_eq_segment] at hs
    have hl : (l+u)/2-(u-l)/2 = l := by ring
    have hu : (l+u)/2+(u-l)/2 = u := by ring
    rw [hl,hu] at hs
    exact (convex_ball _ _).segment_subset hpair.left_mem hpair.right_mem hs
  have hcont : ContinuousOn f (Icc (-1) 1) := by
    intro a ha
    exact ((hS _ (hmap a ha)).continuousAt.comp
      (f := fun a : ℝ => (l+u)/2+(u-l)/2*(a : ℂ)) (by fun_prop)).continuousWithinAt
  have hm := norm_normalizedSemicircleMean_sub_one_le f epsilon hcont (fun a ha => hnorm _ (hmap a ha))
  rw [hillHminusHighContourAction_circuit_formula n r hr K q l u hpair hS hf htrace Γ hΓ,hw,mul_one]
  have hc : (8*((Real.pi : ℂ)*(n : ℕ))) ≠ 0 := by simp [Real.pi_ne_zero,n.ne_zero]
  have he : (8*((Real.pi : ℂ)*(n : ℕ)))*((u-l)^2/(8*((Real.pi : ℂ)*(n : ℕ)))*normalizedSemicircleMean f)-(u-l)^2 =
      (u-l)^2*(normalizedSemicircleMean f-1) := by field_simp [hc]
  change ‖(8*((Real.pi : ℂ)*(n : ℕ)))*((u-l)^2/(8*((Real.pi : ℂ)*(n : ℕ)))*normalizedSemicircleMean f)-(u-l)^2‖ ≤ _
  rw [he,norm_mul,norm_pow]
  exact mul_le_mul_of_nonneg_left hm (sq_nonneg _)

theorem hillHminusHighContourAction_eq_of_winding_eq
    (n : ℕ+) (r : ℝ) (hr : 0 < r) (K : ℂ × PeriodOneHminusOne → ℂ)
    (q : PeriodOneHminusOne) (l u : ℂ) (hpair : HillHminusHighGapPair q n r l u)
    (hS : AnalyticOnNhd ℂ (fun z => hillHminusJointNormalizedGapRoot n r K (z,q))
      (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r)))
    (hf : ∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
      K (z,q) = -hillHminusGapPolynomial n r (z,q)*hillHminusJointNormalizedGapRoot n r K (z,q)^2 /
        (4*((Real.pi : ℂ)*(n : ℕ))^2))
    (htrace : ∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
      squaredCosh (K (z,q)) = (-1 : ℂ)^(n : ℕ)*hillHminusDiscriminant q z/2)
    (Γ Γ₀ : PiecewiseC1Loop)
    (hΓ : Γ.Inside (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) \ segment ℝ l u))
    (hΓ₀ : Γ₀.Inside (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) \ segment ℝ l u))
    (hw : Γ.windingIntegral ((l+u)/2) = Γ₀.windingIntegral ((l+u)/2)) :
    hillHminusHighContourAction n r K q l u Γ = hillHminusHighContourAction n r K q l u Γ₀ := by
  rw [hillHminusHighContourAction_circuit_formula n r hr K q l u hpair hS hf htrace Γ hΓ,
    hillHminusHighContourAction_circuit_formula n r hr K q l u hpair hS hf htrace Γ₀ hΓ₀,hw]

end NLS.KdV
