import NLS.ZakharovShabat.ResolventRectangle
import NLS.FunctionalAnalysis.RectangleResidues

/-!
# Rectangular contour selection of full root spaces

Higher pole terms vanish along every finite Jordan chain. The normalized
rectangular resolvent integral fixes full root spaces strictly inside the
rectangle and annihilates those outside the closed rectangle.
-/

noncomputable section
open Complex Set Classical
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem rectangle_integral_inv_pow_succ {z w a : ℂ}
    (ha : a ∉ RectangleIntegral.boundary z w) (k : ℕ) :
    RectangleIntegral.integral (fun ζ : ℂ => (ζ - a)⁻¹ ^ (k + 1)) z w =
      if k = 0 then RectangleIntegral.integral (fun ζ : ℂ => (ζ - a)⁻¹) z w else 0 := by
  cases k with
  | zero => simp
  | succ k =>
    rw [if_neg (Nat.succ_ne_zero k)]
    exact RectangleIntegral.integral_inv_sub_pow_succ_succ ha k

/-- Weighted rectangular integrals along a finite Jordan chain retain only the simple-pole term. -/
theorem rectangleIntegral_resolvent_root (hp : p ≠ ⊤) (φ : PairSpace p) (z w a : ℂ)
    (hc : RectangleIntegral.boundary z w ⊆ resolventSet hp φ)
    (ha : a ∉ RectangleIntegral.boundary z w)
    (n : ℕ) (x : PairSpace p) (hx : x ∈ periodicRootSpace hp φ a n) (k : ℕ) :
    RectangleIntegral.integral (fun ζ => (ζ - a)⁻¹ ^ k • resolvent hp φ ζ x) z w =
      if k = 0 then RectangleIntegral.integral (fun ζ : ℂ => (ζ - a)⁻¹) z w • x else 0 := by
  induction n generalizing x k with
  | zero =>
    have hx0 : x = 0 := hx
    subst x
    simp [RectangleIntegral.integral]
  | succ n ih =>
    obtain ⟨f, rfl, hf⟩ := (mem_periodicRootSpace_succ hp φ a n x).mp hx
    have hcont := RectangleIntegral.continuousOn_inv_sub ha
    have hR (y : PairSpace p) : ContinuousOn (fun ζ => resolvent hp φ ζ y) (RectangleIntegral.boundary z w) :=
      ((analyticOnNhd_resolvent hp φ).continuousOn.mono hc).clm_apply continuousOn_const
    have heq : RectangleIntegral.integral (fun ζ => (ζ - a)⁻¹ ^ k • resolvent hp φ ζ (domainInclusion f)) z w =
        RectangleIntegral.integral (fun ζ => (ζ - a)⁻¹ ^ (k + 1) • domainInclusion f -
          (ζ - a)⁻¹ ^ (k + 1) • resolvent hp φ ζ (spectralPencil hp φ a f)) z w := by
      apply RectangleIntegral.congr
      intro ζ hζ
      dsimp only
      rw [resolvent_apply_root_step hp φ ζ a (hc hζ) (fun h => ha (h ▸ hζ)),
        smul_sub, smul_smul, smul_smul, ← pow_succ]
    have hi1 : RectangleIntegral.Integrable (fun ζ => (ζ - a)⁻¹ ^ (k + 1) • domainInclusion f) z w :=
      RectangleIntegral.integrable_of_continuousOn ((hcont.pow (k + 1)).smul continuousOn_const)
    have hi2 : RectangleIntegral.Integrable (fun ζ => (ζ - a)⁻¹ ^ (k + 1) •
        resolvent hp φ ζ (spectralPencil hp φ a f)) z w :=
      RectangleIntegral.integrable_of_continuousOn ((hcont.pow (k + 1)).smul (hR (spectralPencil hp φ a f)))
    rw [heq, RectangleIntegral.integral_sub hi1 hi2, ih _ hf (k + 1),
      if_neg (Nat.succ_ne_zero k), sub_zero, RectangleIntegral.integral_smul_const,
      rectangle_integral_inv_pow_succ ha]
    split_ifs <;> simp

/-- A rectangular contour fixes every vector in a strictly enclosed full root space. -/
theorem resolventRectangleIntegral_apply_root (hp : p ≠ ⊤) (φ : PairSpace p) (z w a : ℂ)
    (hc : RectangleIntegral.boundary z w ⊆ resolventSet hp φ)
    (ha : a ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im)
    (x : PairSpace p) (hx : x ∈ periodicRootSpaceTop hp φ a) :
    resolventRectangleIntegral hp φ z w x = x := by
  have hnot : a ∉ RectangleIntegral.boundary z w := by
    rintro ⟨_, _, h | h | h | h⟩ <;> linarith [ha.1.1, ha.1.2, ha.2.1, ha.2.2]
  obtain ⟨n, hn⟩ := (mem_periodicRootSpaceTop hp φ a x).mp hx
  have h := rectangleIntegral_resolvent_root hp φ z w a hc hnot n x hn 0
  simp only [pow_zero, one_smul] at h
  rw [resolventRectangleIntegral_apply hp φ z w hc, h, RectangleIntegral.integral_inv_sub_of_mem ha]
  exact inv_smul_smul₀ (by simp [Real.pi_ne_zero]) _

/-- A rectangular contour annihilates full root spaces outside the filled rectangle. -/
theorem resolventRectangleIntegral_apply_other_root (hp : p ≠ ⊤) (φ : PairSpace p) (z w a : ℂ)
    (hc : RectangleIntegral.boundary z w ⊆ resolventSet hp φ)
    (ha : a ∉ uIcc z.re w.re ×ℂ uIcc z.im w.im)
    (x : PairSpace p) (hx : x ∈ periodicRootSpaceTop hp φ a) :
    resolventRectangleIntegral hp φ z w x = 0 := by
  have hnot : a ∉ RectangleIntegral.boundary z w :=
    fun h => ha (RectangleIntegral.boundary_subset_rectangle z w h)
  obtain ⟨n, hn⟩ := (mem_periodicRootSpaceTop hp φ a x).mp hx
  have h := rectangleIntegral_resolvent_root hp φ z w a hc hnot n x hn 0
  simp only [pow_zero, one_smul] at h
  rw [resolventRectangleIntegral_apply hp φ z w hc, h, RectangleIntegral.integral_inv_sub_of_notMem ha]
  simp

/-- On an enclosed root-space projection, the actual rectangular integral acts as the identity. -/
theorem resolventRectangleIntegral_mul_projection (hp : p ≠ ⊤) (φ : PairSpace p) (z w a : ℂ)
    (hc : RectangleIntegral.boundary z w ⊆ resolventSet hp φ)
    (ha : a ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im) :
    resolventRectangleIntegral hp φ z w * periodicSpectralProjection hp φ a = periodicSpectralProjection hp φ a := by
  apply ContinuousLinearMap.ext
  intro x
  apply resolventRectangleIntegral_apply_root hp φ z w a hc ha
  rw [← range_periodicSpectralProjection hp φ a]
  exact LinearMap.mem_range_self _ x

/-- Exterior root-space projections are annihilated by the actual rectangular contour. -/
theorem resolventRectangleIntegral_mul_projection_eq_zero (hp : p ≠ ⊤) (φ : PairSpace p) (z w a : ℂ)
    (hc : RectangleIntegral.boundary z w ⊆ resolventSet hp φ)
    (ha : a ∉ uIcc z.re w.re ×ℂ uIcc z.im w.im) :
    resolventRectangleIntegral hp φ z w * periodicSpectralProjection hp φ a = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  apply resolventRectangleIntegral_apply_other_root hp φ z w a hc ha
  rw [← range_periodicSpectralProjection hp φ a]
  exact LinearMap.mem_range_self _ x

/-- The rectangular integral selects exactly the enclosed root-space projections; boundary points contribute zero. -/
theorem resolventRectangleIntegral_mul_projection_eq_ite (hp : p ≠ ⊤) (φ : PairSpace p) (z w a : ℂ)
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hc : RectangleIntegral.boundary z w ⊆ resolventSet hp φ) :
    resolventRectangleIntegral hp φ z w * periodicSpectralProjection hp φ a =
      if a ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im then periodicSpectralProjection hp φ a else 0 := by
  classical
  by_cases ha : a ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im
  · rw [if_pos ha]
    exact resolventRectangleIntegral_mul_projection hp φ z w a hc ha
  · rw [if_neg ha]
    by_cases hcl : a ∈ uIcc z.re w.re ×ℂ uIcc z.im w.im
    · have hb := RectangleIntegral.mem_boundary_of_mem_rectangle_of_not_mem_open hre him hcl ha
      rw [(periodicSpectralProjection_eq_zero_iff hp φ a).mpr (hc hb), mul_zero]
    · exact resolventRectangleIntegral_mul_projection_eq_zero hp φ z w a hc hcl

/-- On any finite cluster, the rectangular integral selects precisely the enclosed full root spaces. -/
theorem resolventRectangleIntegral_mul_cluster (hp : p ≠ ⊤) (φ : PairSpace p) (z w : ℂ)
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hc : RectangleIntegral.boundary z w ⊆ resolventSet hp φ) (s : Finset ℂ) :
    resolventRectangleIntegral hp φ z w * periodicClusterProjection hp φ s =
      periodicClusterProjection hp φ (s.filter (fun a => a ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im)) := by
  classical
  rw [periodicClusterProjection, Finset.mul_sum]
  simp_rw [resolventRectangleIntegral_mul_projection_eq_ite hp φ z w _ hre him hc]
  exact (Finset.sum_filter _ _).symm

end NLS.ZakharovShabat
