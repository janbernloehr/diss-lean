import NLS.ZakharovShabat.SourceAngularEtaJointAnnulus
import NLS.ZakharovShabat.SourceStandardRootCauchyZero

/-!
# Joint analytic Cauchy candidates for the eta remainder

The zero-period eta remainder has an explicit joint annular primitive.
Its quotient by the selected root has an interior Cauchy projection,
analytic on the whole enclosing disc. Evaluation at the moving
Dirichlet terminal is analytic through both periodic endpoints and
collapsed gaps, without dividing by the gap displacement.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceAngularEtaQuotientCauchyCandidate
    (hp : p ≠ ⊤) (hp1 : 1 < p) (m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (c : ℂ) (r R : ℝ) (z₀ : ℂ) (ρ : ℝ) : ℂ × CoeffPair p → ℂ :=
  parametricCircleCauchyTransform
    (fun x => sourceAngularEtaRemainderJointAnnularPrimitive hp hp1 m s c r R z₀ x /
      sourceStandardRoot hp hp1 x.2 m x.1) c ρ

def sourceAngularEtaRemainderCauchyCandidate
    (hp : p ≠ ⊤) (hp1 : 1 < p) (m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (c : ℂ) (r R : ℝ) (z₀ : ℂ) (ρ : ℝ) (ψ : CoeffPair p) : ℂ :=
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
  sourceAntiDiscriminantCandidate hp hp1 ψ μ /
      (2*I*sourceStandardRootOmittedProduct hp hp1 m ψ μ) *
    sourceAngularEtaQuotientCauchyCandidate hp hp1 m s c r R z₀ ρ (μ,ψ)

namespace SourceAngularJointAnnulusChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
  {W V : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ} {r R : ℝ} {z₀ : ℂ}

private theorem eta_circle_mem_annulus
    (_D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    (ρ : ℝ) (hrρ : r < ρ) (hρR : ρ < R) (z : ℂ) (hz : z ∈ sphere (c m) ρ) :
    z ∈ ball (c m) R \ closedBall (c m) r := by
  have hd := mem_sphere.mp hz
  exact ⟨mem_ball.mpr (hd.trans_lt hρR),
    fun h => (not_le_of_gt hrρ) (hd ▸ mem_closedBall.mp h)⟩

/-- The interior candidate has no selected-root singularity on the cut or
at its endpoints. It is jointly analytic on the entire fixed disc. -/
theorem analyticOnNhd_etaQuotientCauchyCandidate
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    (ρ : ℝ) (hrρ : r < ρ) (hρR : ρ < R) :
    AnalyticOnNhd ℂ (sourceAngularEtaQuotientCauchyCandidate hp hp1 m s (c m) r R z₀ ρ)
      (ball (c m) ρ ×ˢ V) := by
  have hρ : 0 < ρ := D.inner_pos.trans hrρ
  have hF : AnalyticOnNhd ℂ (fun x : ℂ × CoeffPair p =>
      sourceAngularEtaRemainderJointAnnularPrimitive hp hp1 m s (c m) r R z₀ x /
        sourceStandardRoot hp hp1 x.2 m x.1) (sphere (c m) ρ ×ˢ V) := by
    intro x hx
    have hz := D.eta_circle_mem_annulus ρ hrρ hρR x.1 hx.1
    have hzclosed : x.1 ∈ closedBall (c m) R \ ball (c m) r :=
      ⟨ball_subset_closedBall hz.1,fun h => hz.2 (ball_subset_closedBall h)⟩
    exact (D.analyticOnNhd_etaRemainderJointAnnularPrimitive x ⟨hz,hx.2⟩).div
      (D.selected_root_analytic x ⟨hzclosed,hx.2⟩)
      (sourceStandardRoot_ne_zero_off_segment hp hp1 x.2 m x.1
        (fun h => hz.2 (ball_subset_closedBall (D.gap_enclosed x.2 hx.2 h))))
  exact (analyticOnNhd_parametricCircleCauchyTransform _ (c m) ρ hρ.le V D.source_open hF).mono
    (prod_mono (fun _ hz hs => sphere_disjoint_ball.le_bot ⟨hs,hz⟩) Subset.rfl)

/-- Any constant, including an unknown endpoint normalization depending on
the source, can be removed from the density without changing the candidate. -/
theorem etaQuotientCauchyCandidate_eq_sub_const
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    (ψ : CoeffPair p) (hψ : ψ ∈ V)
    (ρ : ℝ) (hrρ : r < ρ) (hρR : ρ < R) (a z : ℂ) (hz : z ∈ ball (c m) ρ) :
    sourceAngularEtaQuotientCauchyCandidate hp hp1 m s (c m) r R z₀ ρ (z,ψ) =
      circleCauchyTransform (fun w =>
        (sourceAngularEtaRemainderJointAnnularPrimitive hp hp1 m s (c m) r R z₀ (w,ψ)-a) /
          sourceStandardRoot hp hp1 ψ m w) (c m) ρ z := by
  apply (circleCauchyTransform_div_sourceStandardRoot_sub_const hp hp1 ψ m (c m) ρ
    (D.inner_pos.trans hrρ) ((D.gap_enclosed ψ hψ).trans (ball_subset_ball hrρ.le))
    _ _ a z hz).symm
  intro w hw
  exact ((D.analyticOnNhd_etaRemainderJointAnnularPrimitive (w,ψ) ⟨D.eta_circle_mem_annulus ρ hrρ hρR w hw,hψ⟩).comp
    (f := fun w : ℂ => (w,ψ)) (analyticAt_id.prod analyticAt_const)).continuousAt.continuousWithinAt

/-- Any analytic extension of the normalized spectral quotient is recovered
by the explicit candidate. Only agreement on the enclosing circle is needed. -/
theorem etaQuotientCauchyCandidate_eq_of_analytic_extension
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    (ψ : CoeffPair p) (hψ : ψ ∈ V)
    (ρ : ℝ) (hrρ : r < ρ) (hρR : ρ < R) (a : ℂ)
    (H : ℂ → ℂ) (hH : AnalyticOnNhd ℂ H (closedBall (c m) ρ))
    (hboundary : ∀ w ∈ sphere (c m) ρ,
      (sourceAngularEtaRemainderJointAnnularPrimitive hp hp1 m s (c m) r R z₀ (w,ψ)-a) /
        sourceStandardRoot hp hp1 ψ m w = H w)
    (z : ℂ) (hz : z ∈ ball (c m) ρ) :
    sourceAngularEtaQuotientCauchyCandidate hp hp1 m s (c m) r R z₀ ρ (z,ψ) = H z := by
  rw [D.etaQuotientCauchyCandidate_eq_sub_const ψ hψ ρ hrρ hρR a z hz]
  unfold circleCauchyTransform
  have heq : (∮ w in C(c m,ρ),
      ((sourceAngularEtaRemainderJointAnnularPrimitive hp hp1 m s (c m) r R z₀ (w,ψ)-a) /
        sourceStandardRoot hp hp1 ψ m w)/(w-z)) = ∮ w in C(c m,ρ), H w/(w-z) := by
    apply circleIntegral.integral_congr (D.inner_pos.trans hrρ).le
    intro w hw
    change _/(w-z) = H w/(w-z)
    rw [hboundary w hw]
  rw [heq,circleIntegral_div_sub_of_differentiable_on_off_countable countable_empty hz
    hH.continuousOn (fun w hw => (hH w (ball_subset_closedBall hw.1)).differentiableAt),
    ← mul_assoc,inv_mul_cancel₀ (by simp [Real.pi_ne_zero]),one_mul]

/-- The actual moving terminal is a valid analytic evaluation point even
when the selected gap or its anti-discriminant vanishes. -/
theorem analyticAt_etaRemainderCauchyCandidate
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    (ρ : ℝ) (hrρ : r < ρ) (hρR : ρ < R)
    (φ : CoeffPair p) (hφ : φ ∈ V)
    (hμ : AnalyticAt ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) φ) :
    AnalyticAt ℂ (sourceAngularEtaRemainderCauchyCandidate hp hp1 m s (c m) r R z₀ ρ) φ := by
  let μ : CoeffPair p → ℂ := fun ψ => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
  have hgraph : AnalyticAt ℂ (fun ψ => (μ ψ,ψ)) φ := hμ.prod analyticAt_id
  have hP : AnalyticAt ℂ (fun ψ => sourceStandardRootOmittedProduct hp hp1 m ψ (μ ψ)) φ :=
    (D.omitted_analytic (μ φ,φ) ⟨(D.disc_family φ hφ).dirichlet_mem_ball m,hφ⟩).comp
      (x := φ) (f := fun ψ : CoeffPair p => (μ ψ,ψ)) hgraph
  have hanti : AnalyticAt ℂ (fun ψ => sourceAntiDiscriminantCandidate hp hp1 ψ (μ ψ)) φ :=
    (analyticOnNhd_sourceAntiDiscriminantCandidate_joint hp hp1 (μ φ,φ) (mem_univ _)).comp
      (x := φ) (f := fun ψ : CoeffPair p => (μ ψ,ψ)) hgraph
  have hterminal : μ φ ∈ ball (c m) ρ := ball_subset_ball hrρ.le (D.terminal_enclosed φ hφ)
  have hH : AnalyticAt ℂ (fun ψ =>
      sourceAngularEtaQuotientCauchyCandidate hp hp1 m s (c m) r R z₀ ρ (μ ψ,ψ)) φ :=
    (D.analyticOnNhd_etaQuotientCauchyCandidate ρ hrρ hρR (μ φ,φ) ⟨hterminal,hφ⟩).comp
      (x := φ) (f := fun ψ : CoeffPair p => (μ ψ,ψ)) hgraph
  exact (hanti.div (analyticAt_const.mul hP)
    (mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero)
      (sourceStandardRootOmittedProduct_ne_zero hp hp1 φ (μ φ) m
        (((D.disc_family φ hφ).contour_family.2 m).2.2.1
          (ball_subset_closedBall ((D.disc_family φ hφ).dirichlet_mem_ball m)))))).mul hH

theorem analyticAt_etaRemainderCauchyCandidate_of_realSource
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    (ρ : ℝ) (hrρ : r < ρ) (hρR : ρ < R)
    (φ : CoeffPair p) (hφ : φ ∈ V) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    AnalyticAt ℂ (sourceAngularEtaRemainderCauchyCandidate hp hp1 m s (c m) r R z₀ ρ) φ :=
  D.analyticAt_etaRemainderCauchyCandidate ρ hrρ hρR φ hφ
    (analyticAt_canonicalPeriodOneBoundaryRoots_of_realType hp hp1 .dirichlet φ hreal m)

/-- The actual coefficient vanishes at either periodic endpoint; no gap
division or nonzero-gap assumption is needed. -/
theorem etaRemainderCauchyCandidate_eq_zero_of_endpoint
    (_D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    (ψ : CoeffPair p) (_hψ : ψ ∈ V) (ρ : ℝ)
    (hend : SourceAngularDirichletTerminalIsEndpoint hp hp1 ψ m) :
    sourceAngularEtaRemainderCauchyCandidate hp hp1 m s (c m) r R z₀ ρ ψ = 0 := by
  have hw : sourceAntiDiscriminantCandidate hp hp1 ψ
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) = 0 := by
    apply sq_eq_zero_iff.mp
    rw [← sourceDiscriminant_sq_sub_four_at_canonicalDirichletRoot hp hp1 ψ m,
      canonicalDiscriminant_sq_sub_four_eq_pair_mul hp hp1 _ (periodOnePotential_mem ψ) m]
    rcases hend with hleft | hright
    · rw [hleft]; ring
    · rw [hright]; ring
  simp only [sourceAngularEtaRemainderCauchyCandidate,hw,zero_div,zero_mul]

end SourceAngularJointAnnulusChartData
end NLS.ZakharovShabat
