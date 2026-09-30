import NLS.ComplexAnalysis.CirclePrimitiveBounds
import NLS.ComplexAnalysis.QuadraticRootBounds
import NLS.ZakharovShabat.SourceAngularBetaCauchyAnalytic

/-!
# Quantitative beta bounds on actual annular charts

An enclosing-circle bound for the actual gap numerator controls beta
by the actual Dirichlet displacement and gap. The geometric constant
uses only the fixed chart radii, so the argument applies uniformly to
any family of numerators bounded on that circle. No gap division or
regular-terminal hypothesis is used.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The normalized actual Dirichlet coefficient satisfies the selected
quadratic identity, including at either endpoint and at a collapsed gap. -/
theorem sourceDirichletRootCoefficient_sq
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (m : ℤ)
    (hμ : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∈
      sourceStandardRootOmittedDomain hp hp1 ψ m) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
    (sourceAntiDiscriminantCandidate hp hp1 ψ μ /
      (2*I*sourceStandardRootOmittedProduct hp hp1 m ψ μ))^2 =
        sourceAngularSelectedPolynomial hp hp1 ψ m μ := by
  dsimp only
  rw [sourceAngularSelectedPolynomial_eq_endpoint_factor,div_pow,
    ← sourceDiscriminant_sq_sub_four_at_canonicalDirichletRoot hp hp1 ψ m,
    canonicalDiscriminant_sq_sub_four_eq_pair_mul hp hp1 _ (periodOnePotential_mem ψ) m,
    ← sourceStandardRootOmittedProduct_sq_eq_canonicalDeletedPeriodicProduct hp hp1 ψ m _ hμ,
    mul_pow,mul_pow,I_sq]
  have hP := sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ _ m hμ
  field_simp
  ring

/-- Only the gap and the actual terminal displacement enter this bound. -/
theorem norm_sourceDirichletRootCoefficient_le
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (m : ℤ)
    (hμ : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∈
      sourceStandardRootOmittedDomain hp hp1 ψ m) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
    ‖sourceAntiDiscriminantCandidate hp hp1 ψ μ /
      (2*I*sourceStandardRootOmittedProduct hp hp1 m ψ μ)‖ ≤
        ‖μ-sourceStandardRootMidpoint hp hp1 ψ m‖ +
          ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2 := by
  dsimp only
  apply norm_le_of_sq_eq_gap_polynomial
  simpa only [sourceAngularSelectedPolynomial,quadraticRootPolynomial,
    sourcePeriodicGapDisplacement_apply] using sourceDirichletRootCoefficient_sq hp hp1 ψ m hμ

namespace SourceAngularJointAnnulusChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
  {W V : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ} {r R : ℝ} {z₀ : ℂ}

/-- An enclosing circle stays quantitatively separated from both moving
endpoints. This bound is independent of the chosen sheet and gap length. -/
theorem norm_selectedRoot_ge_on_circle
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (ρ : ℝ) (hrρ : r < ρ)
    (w : ℂ) (hw : w ∈ sphere (c m) ρ) :
    ρ-r ≤ ‖sourceStandardRoot hp hp1 ψ m w‖ := by
  have hsep (a : ℂ) (ha : a ∈ sourcePeriodicSegment hp hp1 ψ m) : ρ-r ≤ ‖a-w‖ := by
    have htri := dist_triangle w a (c m)
    rw [mem_sphere.mp hw,dist_comm w a,dist_eq_norm a w] at htri
    have ha := mem_ball.mp (D.gap_enclosed ψ hψ ha)
    linarith
  have havoid : w ∉ sourcePeriodicSegment hp hp1 ψ m := by
    intro h
    have hd := mem_ball.mp (D.gap_enclosed ψ hψ h)
    rw [mem_sphere.mp hw] at hd
    linarith
  exact norm_ge_of_sq_eq_endpoint_product _ _ _ w (ρ-r) (sub_pos.mpr hrρ).le
    (sourceStandardRoot_sq_of_not_mem_segment hp hp1 ψ m w havoid)
    (hsep _ (left_mem_segment ℝ _ _)) (hsep _ (right_mem_segment ℝ _ _))

/-- The normalized primitive estimate reduces the interior quotient to
an actual gap-numerator bound on a single fixed circle. -/
theorem norm_quotientCauchyCandidate_le
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) (hmn : m ≠ n)
    (ρ M : ℝ) (hrρ : r < ρ) (hρR : ρ < R) (hM : 0 ≤ M)
    (hg : ∀ w ∈ sphere (c m) ρ, ‖sourceAngularGapNumerator hp hp1 n m s ψ w‖ ≤ M)
    (z : ℂ) (hz : z ∈ closedBall (c m) r) :
    ‖sourceAngularQuotientCauchyCandidate hp hp1 n m s (c m) r R z₀ ρ (z,ψ)‖ ≤
      Real.pi*ρ^2*M/(ρ-r)^3 := by
  let P : ℂ → ℂ := fun w => sourceAngularJointAnnularPrimitive hp hp1 n s (c m) r R z₀ (w,ψ)
  let Q := sourceStandardRoot hp hp1 ψ m
  let f : ℂ → ℂ := fun w => sourceAngularGapNumerator hp hp1 n m s ψ w/Q w
  have hρ : 0 < ρ := D.inner_pos.trans hrρ
  have hδ : 0 < ρ-r := sub_pos.mpr hrρ
  have hQ (w : ℂ) (hw : w ∈ sphere (c m) ρ) : ρ-r ≤ ‖Q w‖ :=
    D.norm_selectedRoot_ge_on_circle ψ hψ ρ hrρ w hw
  have hP (w : ℂ) (hw : w ∈ sphere (c m) ρ) : HasDerivAt P (f w) w := by
    rw [show f w = sourceAngularIntegrand n s (sourceCanonicalRootJointProduct hp hp1) (w,ψ) from
      (sourceAngularIntegrand_eq_gapNumerator_div_standardRoot hp hp1 n m s ψ w).symm]
    apply D.spectral_derivative n hmn ψ hψ w
    have hd := mem_sphere.mp hw
    exact ⟨mem_ball.mpr (hd.trans_lt hρR),
      fun h => (not_le_of_gt hrρ) (hd ▸ mem_closedBall.mp h)⟩
  have hf (w : ℂ) (hw : w ∈ sphere (c m) ρ) : ‖f w‖ ≤ M/(ρ-r) := by
    rw [show f w = sourceAngularGapNumerator hp hp1 n m s ψ w/Q w from rfl,norm_div]
    exact div_le_div₀ hM (hg w hw) hδ (hQ w hw)
  have hzρ : z ∈ ball (c m) ρ := mem_ball.mpr ((mem_closedBall.mp hz).trans_lt hrρ)
  rw [D.quotientCauchyCandidate_eq_sub_const ψ hψ n ρ hrρ hρR (P (c m+ρ)) z hzρ]
  have h := norm_circleCauchyTransform_primitive_quotient_le P f Q (c m) ρ r (ρ-r) (M/(ρ-r))
    hρ.le hrρ hδ (by positivity) hP hf hQ z hz
  convert h using 1
  field_simp

/-- Quantitative reduction for the actual beta, valid throughout the
complex chart, including collapsed gaps and endpoint terminals. -/
theorem norm_beta_le_of_gapNumerator_bound
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) (hmn : m ≠ n)
    (ρ M : ℝ) (hrρ : r < ρ) (hρR : ρ < R) (hM : 0 ≤ M)
    (hg : ∀ w ∈ sphere (c m) ρ, ‖sourceAngularGapNumerator hp hp1 n m s ψ w‖ ≤ M) :
    ‖sourceAngularBeta hp hp1 n m s ψ‖ ≤
      (‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m-
          sourceStandardRootMidpoint hp hp1 ψ m‖ + ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2) *
        (Real.pi*ρ^2*M/(ρ-r)^3) := by
  rw [← D.betaCauchyCandidate_eq_beta ψ hψ n hmn ρ hrρ hρR]
  dsimp only [sourceAngularBetaCauchyCandidate]
  rw [norm_mul]
  apply mul_le_mul
  · exact norm_sourceDirichletRootCoefficient_le hp hp1 ψ m
      (((D.disc_family ψ hψ).contour_family.2 m).2.2.1
        (ball_subset_closedBall ((D.disc_family ψ hψ).dirichlet_mem_ball m)))
  · exact D.norm_quotientCauchyCandidate_le ψ hψ n hmn ρ M hrρ hρR hM hg _
      (ball_subset_closedBall (D.terminal_enclosed ψ hψ))
  · exact norm_nonneg _
  · positivity

end SourceAngularJointAnnulusChartData
end NLS.ZakharovShabat
