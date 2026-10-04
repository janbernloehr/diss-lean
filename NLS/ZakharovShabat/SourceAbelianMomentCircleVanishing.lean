import NLS.ZakharovShabat.SourceAbelianMomentCancellation

/-! # Odd and collapsed-gap moment vanishing on isolating circles

The regular integrands extend analytically to the entire filled circle.
Cauchy's theorem proves the two vanishing identities in Lemma 20.1.
The argument works for every entire psi candidate, so in particular for
the actual normalized branch, without separating its omitted index.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

/-- Every intermediate circle avoids all gaps, uniformly on the source ball. -/
theorem intermediate_circle_root
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (k : ℤ)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius)
    (R : ℝ) (hinner : C.discs.inner k ≤ R) (houter : R < C.discs.outer k)
    (z : ℂ) (hz : z ∈ sphere (C.discs.center k) R) :
    z ∈ sourceCanonicalRootDomain hp hp1 ψ := by
  intro j hj
  by_cases he : j = k
  · subst j
    have hlt := mem_ball.mp (C.discs.segment_subset ψ hψ k hj)
    rw [mem_sphere.mp hz] at hlt
    exact (not_lt_of_ge hinner) hlt
  · exact C.discs.avoids_other ψ hψ k
      (closedBall_subset_closedBall houter.le (sphere_subset_closedBall hz)) j he hj

private theorem momentCircle_zero_of_extension
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (n k : ℤ) (m : ℕ)
    (a : Coeff p) (ψ : CoeffPair p) (R : ℝ) (hR : 0 ≤ R) (houter : R < C.discs.outer k)
    (H : ℂ → ℂ) (hH : AnalyticOnNhd ℂ H (ball (C.discs.center k) (C.discs.outer k)))
    (he : ∀ z ∈ sphere (C.discs.center k) R,
      sourceAbelianMomentIntegrand hp hp1 W n k m (z,(a,ψ)) = H z) :
    sourceAbelianMomentCircle hp hp1 W n k m a ψ (C.discs.center k) R = 0 := by
  have hd : DifferentiableOn ℂ H (closedBall (C.discs.center k) R) :=
    fun z hz => (hH z (closedBall_subset_ball houter hz)).differentiableAt.differentiableWithinAt
  have hzero := (DiffContOnCl.mk_ball (hd.mono ball_subset_closedBall) hd.continuousOn).circleIntegral_eq_zero hR
  unfold sourceAbelianMomentCircle
  rw [← hzero]
  exact circleIntegral.integral_congr hR he

/-- Lemma 20.1(iii) on each assigned intermediate circle, for every
numerator index and every odd order. -/
theorem momentCircle_odd_eq_zero
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (n k : ℤ) (l : ℕ)
    (a : Coeff p) (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hO : AnalyticOnNhd ℂ (sourceStandardRootOmittedProduct hp hp1 k ψ)
      (sourceStandardRootOmittedDomain hp hp1 ψ k))
    (R : ℝ) (hinner : C.discs.inner k ≤ R) (houter : R < C.discs.outer k) :
    sourceAbelianMomentCircle hp hp1 W n k (2*l+1) a ψ (C.discs.center k) R = 0 := by
  let Q : ℂ → ℂ := fun z => sourceFullAbelianCauchyQuotient hp hp1 W k (C.discs.center k) (C.discs.outer k) (z,ψ)
  let B := sourceMomentRegularNumerator hp hp1 n k a ψ
  let H : ℂ → ℂ := fun z => (C.square k (z,ψ))^l*(Q z*B z)
  have hB : AnalyticOnNhd ℂ B (ball (C.discs.center k) (C.discs.outer k)) :=
    (sourceMomentRegularNumerator_analyticOnNhd hp hp1 n k a ψ hO).mono
      (fun z hz => C.discs.avoids_other ψ hψ k (ball_subset_closedBall hz))
  have hH : AnalyticOnNhd ℂ H (ball (C.discs.center k) (C.discs.outer k)) := by
    intro z hz
    exact ((C.square_analytic k ψ hψ z hz).pow l).mul
      ((C.quotient_slice_analytic k ψ hψ z hz).mul (hB z hz))
  apply momentCircle_zero_of_extension C n k (2*l+1) a ψ R
    ((C.discs.inner_pos k).le.trans hinner) houter H hH
  intro z hz
  exact C.momentIntegrand_odd_eq_regular n k l a ψ hψ z
    ⟨closedBall_subset_ball houter (sphere_subset_closedBall hz),
      C.intermediate_circle_root k ψ hψ R hinner houter z hz k⟩

/-- Lemma 20.1(iv): every positive-order moment vanishes at a collapsed
gap, for the diagonal and off-diagonal numerator indices alike. -/
theorem momentCircle_succ_eq_zero_of_collapsed
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (n k : ℤ) (m : ℕ)
    (a : Coeff p) (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hO : AnalyticOnNhd ℂ (sourceStandardRootOmittedProduct hp hp1 k ψ)
      (sourceStandardRootOmittedDomain hp hp1 ψ k))
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) k = 0)
    (R : ℝ) (hinner : C.discs.inner k ≤ R) (houter : R < C.discs.outer k) :
    sourceAbelianMomentCircle hp hp1 W n k (m+1) a ψ (C.discs.center k) R = 0 := by
  let Q : ℂ → ℂ := fun z => sourceFullAbelianCauchyQuotient hp hp1 W k (C.discs.center k) (C.discs.outer k) (z,ψ)
  let B := sourceMomentRegularNumerator hp hp1 n k a ψ
  let H : ℂ → ℂ := fun z => ((sourceStandardRootMidpoint hp hp1 ψ k-z)*Q z)^m*(Q z*B z)
  have hB : AnalyticOnNhd ℂ B (ball (C.discs.center k) (C.discs.outer k)) :=
    (sourceMomentRegularNumerator_analyticOnNhd hp hp1 n k a ψ hO).mono
      (fun z hz => C.discs.avoids_other ψ hψ k (ball_subset_closedBall hz))
  have hH : AnalyticOnNhd ℂ H (ball (C.discs.center k) (C.discs.outer k)) := by
    intro z hz
    exact (((analyticAt_const.sub analyticAt_id).mul (C.quotient_slice_analytic k ψ hψ z hz)).pow m).mul
      ((C.quotient_slice_analytic k ψ hψ z hz).mul (hB z hz))
  apply momentCircle_zero_of_extension C n k (m+1) a ψ R
    ((C.discs.inner_pos k).le.trans hinner) houter H hH
  intro z hz
  exact C.momentIntegrand_succ_eq_regular_of_collapsed n k m a ψ hψ hgap z
    ⟨closedBall_subset_ball houter (sphere_subset_closedBall hz),
      C.intermediate_circle_root k ψ hψ R hinner houter z hz k⟩

end NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
