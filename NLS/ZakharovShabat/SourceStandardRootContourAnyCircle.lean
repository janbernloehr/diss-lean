import NLS.ZakharovShabat.SourceStandardRootContourMidpoint

/-!
# Diagonal standard-root integral on arbitrary enclosing circles

A shifted inversion computes the reciprocal root integral on sufficiently
large circles about any center. Analyticity off the periodic gap and the
annulus theorem carry this value to every circle strictly enclosing the
closed gap segment.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The holomorphic factor appearing after inversion about an arbitrary
circle center. -/
def shiftedInverseRootFactor (t g c u : ℂ) : ℂ :=
  ((1-(t-c)*u) *
    Complex.sqrt (1-(g/4)*u^2/(1-(t-c)*u)^2))⁻¹

@[simp] theorem shiftedInverseRootFactor_zero (t g c : ℂ) :
    shiftedInverseRootFactor t g c 0 = 1 := by
  simp [shiftedInverseRootFactor]

/-- The shifted inverse-root factor is analytic at the inverted origin. -/
theorem shiftedInverseRootFactor_analyticAt_zero (t g c : ℂ) :
    AnalyticAt ℂ (shiftedInverseRootFactor t g c) 0 := by
  let B : ℂ → ℂ := fun u => 1-(t-c)*u
  let P : ℂ → ℂ := fun u => 1-(g/4)*u^2/(B u)^2
  have hB : AnalyticAt ℂ B 0 := by
    dsimp [B]
    exact analyticAt_const.sub (analyticAt_const.mul analyticAt_id)
  have hB0 : (B 0)^2 ≠ 0 := by simp [B]
  have hP : AnalyticAt ℂ P 0 := by
    dsimp [P]
    exact analyticAt_const.sub
      ((analyticAt_const.mul (analyticAt_id.pow 2)).div (hB.pow 2) hB0)
  have hP0 : P 0 = 1 := by simp [P, B]
  have hsqrt : AnalyticAt ℂ Complex.sqrt (P 0) := by
    rw [hP0]
    exact Complex.differentiableOn_sqrt.analyticAt
      (Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane)
  have hcomp : AnalyticAt ℂ (fun u => Complex.sqrt (P u)) 0 :=
    hsqrt.comp hP
  have hprod : AnalyticAt ℂ
      (fun u => B u * Complex.sqrt (P u)) 0 := hB.mul hcomp
  have hprod0 : B 0 * Complex.sqrt (P 0) ≠ 0 := by simp [B, hP0]
  exact hprod.inv hprod0

/-- On a circle avoiding the center and midpoint, the reciprocal root
is a simple reciprocal pole times the shifted holomorphic factor. -/
theorem normalizedRoot_inv_shifted_factor (t g c z : ℂ)
    (hzc : z ≠ c) (hzt : z ≠ t) :
    (normalizedStandardRoot t g z)⁻¹ =
      -((z-c)⁻¹) * shiftedInverseRootFactor t g c ((z-c)⁻¹) := by
  let u : ℂ := (z-c)⁻¹
  let B : ℂ := 1-(t-c)*u
  have hzc' : z-c ≠ 0 := sub_ne_zero.mpr hzc
  have hzt' : z-t ≠ 0 := sub_ne_zero.mpr hzt
  have hBmul : (z-c)*B = z-t := by
    dsimp [B, u]
    field_simp [hzc']
    ring
  have hB : B ≠ 0 := by
    intro he
    rw [he, mul_zero] at hBmul
    exact hzt' hBmul.symm
  have htz : t-z ≠ 0 := sub_ne_zero.mpr hzt.symm
  have hrad : 1-g/(4*(t-z)^2) = 1-(g/4)*u^2/B^2 := by
    have htzeq : t-z = -((z-c)*B) := by rw [hBmul]; ring
    rw [htzeq]
    dsimp [u]
    field_simp [hzc', hB]
  unfold normalizedStandardRoot shiftedInverseRootFactor
  change ((t-z)*Complex.sqrt (1-g/(4*(t-z)^2)))⁻¹ =
    -u * (B*Complex.sqrt (1-(g/4)*u^2/B^2))⁻¹
  rw [hrad]
  have htzeq : t-z = -((z-c)*B) := by rw [hBmul]; ring
  rw [htzeq]
  simp only [mul_inv_rev, inv_neg]
  dsimp [u]
  ring

/-- Every sufficiently large circle about any chosen center has the
diagonal reciprocal-root integral `−2πi`. -/
theorem eventually_circleIntegral_normalizedRoot_inv_any_center
    (t g c : ℂ) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ < R →
      (∮ z in C(c, R), (normalizedStandardRoot t g z)⁻¹) =
        -(2*Real.pi*Complex.I) := by
  let H : ℂ → ℂ := shiftedInverseRootFactor t g c
  obtain ⟨ρ, hρ, hHOn⟩ :=
    (shiftedInverseRootFactor_analyticAt_zero t g c).exists_ball_analyticOnNhd
  let R₀ : ℝ := max ‖t-c‖ ρ⁻¹
  have hR₀ : 0 < R₀ :=
    (inv_pos.mpr hρ).trans_le (le_max_right _ _)
  refine ⟨R₀, hR₀, ?_⟩
  intro R hR₀R
  have hR : 0 < R := hR₀.trans hR₀R
  have htcR : ‖t-c‖ < R := (le_max_left _ _).trans_lt hR₀R
  have hρinvR : ρ⁻¹ < R := (le_max_right _ _).trans_lt hR₀R
  have hρR : 1 < ρ*R := by
    have h := mul_lt_mul_of_pos_left hρinvR hρ
    simpa only [mul_inv_cancel₀ hρ.ne'] using h
  have hRinvρ : R⁻¹ < ρ := by
    rw [show R⁻¹ = 1/R by ring]
    exact (div_lt_iff₀ hR).2 (by nlinarith [hρR])
  have hHdiff : DifferentiableOn ℂ H (closedBall (0:ℂ) |R⁻¹|) := by
    intro u hu
    have hnorm : ‖u‖ ≤ R⁻¹ := by
      simpa only [mem_closedBall, dist_zero_right,
        abs_of_pos (inv_pos.mpr hR)] using hu
    have huρ : u ∈ ball (0:ℂ) ρ := by
      simpa only [mem_ball, dist_zero_right] using lt_of_le_of_lt hnorm hRinvρ
    exact (hHOn u huρ).differentiableAt.differentiableWithinAt
  have hH : DiffContOnCl ℂ H (ball (0:ℂ) |R⁻¹|) :=
    DiffContOnCl.mk_ball (hHdiff.mono ball_subset_closedBall) hHdiff.continuousOn
  have heq : (∮ z in C(c, R), (normalizedStandardRoot t g z)⁻¹) =
      ∮ z in C(c, R), -((z-c)⁻¹) * H ((z-c)⁻¹) := by
    apply circleIntegral.integral_congr hR.le
    intro z hz
    have hzc : z ≠ c := by
      intro he
      have hbad := mem_sphere.mp hz
      rw [he, dist_self] at hbad
      linarith
    have hzt : z ≠ t := by
      intro he
      have hbad := mem_sphere.mp hz
      rw [he, dist_eq_norm] at hbad
      exact (ne_of_lt htcR) hbad
    exact normalizedRoot_inv_shifted_factor t g c z hzc hzt
  rw [heq]
  have hneg : (∮ z in C(c, R), -((z-c)⁻¹) * H ((z-c)⁻¹)) =
      -(∮ z in C(c, R), (z-c)⁻¹ * H ((z-c)⁻¹)) := by
    have heq' : (fun z : ℂ => -((z-c)⁻¹) * H ((z-c)⁻¹)) =
        (fun z : ℂ => (-1)*((z-c)⁻¹ * H ((z-c)⁻¹))) := by
      funext z; ring
    rw [heq', circleIntegral.integral_const_mul]
    ring
  rw [hneg, circleIntegral_inverse_pulled_holomorphic H c R hR hH]
  simp [H]

/-- The reciprocal source root has the same circle integral across an
annulus disjoint from its closed gap. -/
theorem circleIntegral_sourceStandardRoot_inv_annulus
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (c : ℂ) (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R)
    (hseg : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c r) :
    (∮ z in C(c, R), (sourceStandardRoot hp hp1 ψ n z)⁻¹) =
      ∮ z in C(c, r), (sourceStandardRoot hp hp1 ψ n z)⁻¹ := by
  let f : ℂ → ℂ := fun z => (sourceStandardRoot hp hp1 ψ n z)⁻¹
  have hdiff (z : ℂ) (hz : z ∉ ball c r) : DifferentiableAt ℂ f z := by
    apply (sourceStandardRoot_inv_analyticAt hp hp1 ψ n z ?_).differentiableAt
    intro hzin
    exact hz (hseg hzin)
  apply Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
    hr hrR (s := ∅) Set.countable_empty
  · intro z hz
    exact (hdiff z hz.2).continuousAt.continuousWithinAt
  · intro z hz
    exact hdiff z (fun h => hz.1.2 (ball_subset_closedBall h))

/-- The source reciprocal root has diagonal integral `−2πi` on every
sufficiently large circle about any center. -/
theorem eventually_circleIntegral_sourceStandardRoot_inv_any_center
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (c : ℂ) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ < R →
      (∮ z in C(c, R), (sourceStandardRoot hp hp1 ψ n z)⁻¹) =
        -(2*Real.pi*Complex.I) := by
  let t := canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let d := canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  simpa only [sourceStandardRoot, t, d] using
    eventually_circleIntegral_normalizedRoot_inv_any_center t (d^2) c

/-- Every positively oriented circle strictly enclosing the closed
periodic gap has diagonal reciprocal-root integral `−2πi`. -/
theorem circleIntegral_sourceStandardRoot_inv_of_gap_mem_ball
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hseg : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c r) :
    (∮ z in C(c, r), (sourceStandardRoot hp hp1 ψ n z)⁻¹) =
      -(2*Real.pi*Complex.I) := by
  obtain ⟨R₀, hR₀, hlarge⟩ :=
    eventually_circleIntegral_sourceStandardRoot_inv_any_center hp hp1 ψ n c
  let R : ℝ := max r R₀ + 1
  have hrR : r ≤ R := by dsimp [R]; linarith [le_max_left r R₀]
  have hR₀R : R₀ < R := by dsimp [R]; linarith [le_max_right r R₀]
  calc
    (∮ z in C(c, r), (sourceStandardRoot hp hp1 ψ n z)⁻¹) =
        ∮ z in C(c, R), (sourceStandardRoot hp hp1 ψ n z)⁻¹ :=
      (circleIntegral_sourceStandardRoot_inv_annulus hp hp1 ψ n c r R hr hrR hseg).symm
    _ = -(2*Real.pi*Complex.I) := hlarge R hR₀R

/-- The normalized diagonal contour value is `−1` for every circle
strictly enclosing the indexed gap. -/
theorem normalized_circleIntegral_sourceStandardRoot_inv_of_gap_mem_ball
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hseg : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c r) :
    (2*Real.pi*Complex.I)⁻¹ *
      (∮ z in C(c, r), (sourceStandardRoot hp hp1 ψ n z)⁻¹) = -1 := by
  rw [circleIntegral_sourceStandardRoot_inv_of_gap_mem_ball hp hp1 ψ n c r hr hseg]
  have hnonzero : (2*Real.pi*Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero]
  calc
    (2*Real.pi*Complex.I)⁻¹ * -(2*Real.pi*Complex.I) =
        -((2*Real.pi*Complex.I)⁻¹ * (2*Real.pi*Complex.I)) := by ring
    _ = -1 := by rw [inv_mul_cancel₀ hnonzero]

end NLS.ZakharovShabat
