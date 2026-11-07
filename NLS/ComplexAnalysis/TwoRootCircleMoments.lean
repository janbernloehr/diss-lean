import NLS.ComplexAnalysis.WeightedArgumentPrinciple
import NLS.ComplexAnalysis.ParametricCircleIntegralHigher
import NLS.ComplexAnalysis.JointSpectralDerivative

/-! # Analytic symmetric coordinates of a two-root cluster

Fixed logarithmic-derivative contours recover root power sums with exact
multiplicity. They define analytic symmetric coordinates without choosing
an ordering or assuming distinct roots.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped Classical
namespace NLS.ComplexAnalysis
variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

/-- The original logarithmic-derivative contour, with its residue normalization. -/
def logarithmicCircleMoment (F : ℂ × A → ℂ) (c : ℂ) (R : ℝ) (k : ℕ) (a : A) : ℂ :=
  (2*Real.pi*I : ℂ)⁻¹ * ∮ z in C(c,R), z^k * logDeriv (fun w => F (w,a)) z

/-- Nonvanishing on a fixed contour makes its power moments analytic in
the Banach parameter. No root labeling is needed. -/
theorem analyticOnNhd_logarithmicCircleMoment
    (F : ℂ × A → ℂ) (hF : AnalyticOnNhd ℂ F univ)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R) (k : ℕ)
    (V : Set A) (hV : IsOpen V)
    (hb : ∀ a ∈ V, ∀ z ∈ sphere c R, F (z,a) ≠ 0) :
    AnalyticOnNhd ℂ (logarithmicCircleMoment F c R k) V := by
  let D : Set (ℂ × A) := {t | F t ≠ 0}
  have hD : IsOpen D := isOpen_ne_fun hF.continuous continuous_const
  let ev : ((ℂ × A) →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ (1,0)
  have hd : AnalyticOnNhd ℂ (fun t => (fderiv ℂ F t) (1,0)) univ :=
    ev.comp_analyticOnNhd hF.fderiv
  let G : ℂ × A → ℂ := fun t => t.1^k * (fderiv ℂ F t) (1,0) / F t
  have hG : AnalyticOnNhd ℂ G D := by
    intro t ht
    exact (((analyticAt_fst.pow k).mul (hd t (mem_univ _))).div
      (hF t (mem_univ _)) ht)
  have hc := analyticOnNhd_circleIntegral_of_jointAnalytic G hD hG c R hR hV hb
  intro a ha
  apply (analyticAt_const.mul (hc a ha)).congr
  apply Filter.Eventually.of_forall
  intro b
  change (2*Real.pi*I : ℂ)⁻¹ * (∮ z in C(c,R), G (z,b)) = _
  congr 1
  apply circleIntegral.integral_congr hR
  intro z _
  dsimp [G, logDeriv]
  rw [deriv_spectral_section_eq_fderiv F z b (hF (z,b) (mem_univ _)).differentiableAt]
  ring

omit [NormedAddCommGroup A] [NormedSpace ℂ A] in
/-- The contour moment is the sum of the two actual root powers,
including the multiplicity two of a repeated root. -/
theorem logarithmicCircleMoment_eq_pair
    (F : ℂ × A → ℂ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (a : A) (l u : ℂ)
    (hf : AnalyticOnNhd ℂ (fun z => F (z,a)) (closedBall c R))
    (hl : l ∈ ball c R) (hu : u ∈ ball c R)
    (hzeros : ∀ z ∈ closedBall c R, F (z,a) = 0 ↔ z = l ∨ z = u)
    (hmult : ∀ z ∈ closedBall c R,
      analyticOrderNatAt (fun w => F (w,a)) z = ({l,u} : Multiset ℂ).count z)
    (k : ℕ) : logarithmicCircleMoment F c R k a = l^k+u^k := by
  have hb (z : ℂ) (hz : z ∈ sphere c R) : F (z,a) ≠ 0 := by
    intro he
    rcases (hzeros z (sphere_subset_closedBall hz)).mp he with rfl | rfl
    · exact sphere_disjoint_ball.le_bot ⟨hz,hl⟩
    · exact sphere_disjoint_ball.le_bot ⟨hz,hu⟩
  have hw : c+(R : ℂ) ∈ sphere c R := by simp [abs_of_pos hR]
  have hfinite (z : ℂ) (hz : z ∈ closedBall c R) :
      analyticOrderAt (fun w => F (w,a)) z ≠ ⊤ :=
    analyticOrderAt_ne_top_on_connected (isConnected_closedBall hR.le).isPreconnected
      hf (sphere_subset_closedBall hw) (hb _ hw) hz
  have hs : (({l,u} : Finset ℂ) : Set ℂ) ⊆ ball c R := by
    intro z hz
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  have hi := circleIntegral_weighted_logDeriv_eq_sum hR hf (analyticOnNhd_id.pow k)
    hb hfinite {l,u} hs (fun z hz he => by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using (hzeros z hz).mp he)
  have hsum : (∑ z ∈ ({l,u} : Finset ℂ),
      (analyticOrderNatAt (fun w => F (w,a)) z : ℂ)*z^k) = l^k+u^k := by
    trans ∑ z ∈ ({l,u} : Finset ℂ), (({l,u} : Multiset ℂ).count z : ℂ)*z^k
    · apply Finset.sum_congr rfl
      intro z hz
      rw [hmult z (ball_subset_closedBall (hs hz))]
    · by_cases hlu : l = u
      · rw [← hlu]
        simp [two_mul]
      · simp [hlu, Ne.symm hlu]
  simp only [Pi.pow_apply] at hi
  rw [hsum] at hi
  rw [logarithmicCircleMoment, hi, ← mul_assoc,
    inv_mul_cancel₀ (by simp [Real.pi_ne_zero]), one_mul]

/-- Monic two-root factor expressed using only the first two moments. -/
def momentPairPolynomial (F : ℂ × A → ℂ) (c : ℂ) (R : ℝ) (t : ℂ × A) : ℂ :=
  t.1^2-logarithmicCircleMoment F c R 1 t.2*t.1 +
    (logarithmicCircleMoment F c R 1 t.2^2-logarithmicCircleMoment F c R 2 t.2)/2

omit [NormedAddCommGroup A] [NormedSpace ℂ A] in
theorem momentPairPolynomial_eq (F : ℂ × A → ℂ) (c : ℂ) (R : ℝ)
    (a : A) (l u z : ℂ)
    (h₁ : logarithmicCircleMoment F c R 1 a = l+u)
    (h₂ : logarithmicCircleMoment F c R 2 a = l^2+u^2) :
    momentPairPolynomial F c R (z,a) = (z-l)*(z-u) := by
  dsimp only [momentPairPolynomial]
  rw [h₁,h₂]
  ring

theorem analyticOnNhd_momentPairPolynomial
    (F : ℂ × A → ℂ) (hF : AnalyticOnNhd ℂ F univ)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R) (V : Set A) (hV : IsOpen V)
    (hb : ∀ a ∈ V, ∀ z ∈ sphere c R, F (z,a) ≠ 0) :
    AnalyticOnNhd ℂ (momentPairPolynomial F c R) (univ ×ˢ V) := by
  have h₁ := analyticOnNhd_logarithmicCircleMoment F hF c R hR 1 V hV hb
  have h₂ := analyticOnNhd_logarithmicCircleMoment F hF c R hR 2 V hV hb
  intro t ht
  have h₁t := (h₁ t.2 ht.2).comp (analyticAt_snd (p := t))
  have h₂t := (h₂ t.2 ht.2).comp (analyticAt_snd (p := t))
  exact ((analyticAt_fst.pow 2).sub (h₁t.mul analyticAt_fst)).add
    ((h₁t.pow 2).sub h₂t).div_const

end NLS.ComplexAnalysis
