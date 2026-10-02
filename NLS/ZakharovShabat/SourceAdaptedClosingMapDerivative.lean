import NLS.ZakharovShabat.SourceAdaptedClosingMap
import NLS.ZakharovShabat.WeightedResonantCenterRemainderDerivative

/-!
# The adapted source map is uniformly close to the identity

Isometric period-one transport and first-component reflection preserve
the actual remainder estimates. The adapted source map is analytic on
one fixed ball, its derivative is arbitrarily close to the identity,
and its derivative has a common Lipschitz bound for every larger cutoff.
-/

noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The full source remainder derivative is the isometric transport
of the actual weighted physical remainder derivative. -/
theorem fderiv_sourceResonantCenterRemainder (hp : p ≠ ⊤) (φ : CoeffPair p) (N : ℕ)
    (hR : DifferentiableAt ℂ (fun χ => weightedResonantCenterRemainder hp SpectralWeight.one χ N)
      (sourceWeightedPeriodOne φ)) :
    fderiv ℂ (fun ψ => sourceResonantCenterRemainder hp ψ N) φ =
      sourceClosingReflection.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((fderiv ℂ (fun χ => weightedResonantCenterRemainder hp SpectralWeight.one χ N)
          (sourceWeightedPeriodOne φ)).comp sourceWeightedPeriodOne.toContinuousLinearMap) :=
  ((sourceClosingReflection (p := p)).toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp φ
    (hR.hasFDerivAt.comp φ (sourceWeightedPeriodOne (p := p)).toContinuousLinearMap.hasFDerivAt)).fderiv

/-- The derivative of the adapted source map is the identity plus
the actual transported remainder derivative. -/
theorem fderiv_sourceAdaptedClosingMap (hp : p ≠ ⊤) (φ : CoeffPair p) (N : ℕ)
    (hR : DifferentiableAt ℂ (fun ψ => sourceResonantCenterRemainder hp ψ N) φ) :
    fderiv ℂ (fun ψ => sourceAdaptedClosingMap hp ψ N) φ =
      ContinuousLinearMap.id ℂ (CoeffPair p)+fderiv ℂ (fun ψ => sourceResonantCenterRemainder hp ψ N) φ :=
  ((hasFDerivAt_id φ).add hR.hasFDerivAt).fderiv

/-- One fixed source ball carries the actual adapted spectral map,
its quadratic difference from the identity, its arbitrarily small
derivative difference, and a common derivative Lipschitz bound.
Actual sequence membership is constructed throughout the outer ball. -/
theorem exists_fixedBall_sourceAdaptedClosingMap_derivative
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (η : ℝ) (hη : 0 < η) :
    let K := resonantCenterRemainderBallConstant p (‖φ‖+1);
    ∃ r : ℝ, 0 < r ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      AnalyticOnNhd ℂ (fun ψ => sourceAdaptedClosingMap hp ψ N) (ball φ (4*r)) ∧
      (∀ ψ ∈ ball φ (4*r),
        (∀ positive : Bool, Memℓp (weightedResonantCenterRemainderCoordinate hp SpectralWeight.one
          (sourceWeightedPeriodOne ψ) N positive) p) ∧
        ‖sourceAdaptedClosingMap hp ψ N-ψ‖ ≤ K*r^2) ∧
      (∀ ψ ∈ ball φ (3*r),
        ‖fderiv ℂ (fun χ => sourceAdaptedClosingMap hp χ N) ψ-ContinuousLinearMap.id ℂ (CoeffPair p)‖ < η) ∧
      ∀ x ∈ ball φ r, ∀ y ∈ ball φ r,
        ‖fderiv ℂ (fun χ => sourceAdaptedClosingMap hp χ N) y-
          fderiv ℂ (fun χ => sourceAdaptedClosingMap hp χ N) x‖ ≤ 4*K*‖y-x‖ := by
  obtain ⟨r,hr,N₀,hN₀,hR⟩ := exists_fixedBall_weightedResonantCenterRemainder_derivative
    hp hp1 SpectralWeight.one (sourceWeightedPeriodOne φ) η hη
  simp only [norm_sourceWeightedPeriodOne] at hR
  have hE {s : ℝ} {ψ : CoeffPair p} (hψ : ψ ∈ ball φ s) :
      sourceWeightedPeriodOne ψ ∈ ball (sourceWeightedPeriodOne φ) s := by
    rw [mem_ball,dist_eq_norm,← map_sub,norm_sourceWeightedPeriodOne]
    simpa only [mem_ball,dist_eq_norm] using hψ
  refine ⟨r,hr,N₀,hN₀,?_⟩
  intro N hN
  have h := hR N hN
  have hinner : ball φ (3*r) ⊆ ball φ (4*r) := ball_subset_ball (by linarith)
  have hsmall : ball φ r ⊆ ball φ (4*r) := ball_subset_ball (by linarith)
  have hA : AnalyticOnNhd ℂ (fun ψ => sourceResonantCenterRemainder hp ψ N) (ball φ (4*r)) := by
    intro ψ hψ
    have hχ : AnalyticAt ℂ (fun ξ : CoeffPair p => weightedResonantCenterRemainder hp SpectralWeight.one
        (sourceWeightedPeriodOne ξ) N) ψ :=
      (h.1 (sourceWeightedPeriodOne ψ) (hE hψ)).comp
        (sourceWeightedPeriodOne.toContinuousLinearMap.analyticAt ψ)
    exact (sourceClosingReflection.toContinuousLinearEquiv.toContinuousLinearMap.analyticAt _).comp hχ
  have hder (ψ : CoeffPair p) (hψ : ψ ∈ ball φ (4*r)) :=
    fderiv_sourceResonantCenterRemainder hp ψ N (h.1 (sourceWeightedPeriodOne ψ) (hE hψ)).differentiableAt
  refine ⟨?_,?_,?_,?_⟩
  · intro ψ hψ
    exact analyticAt_id.add (hA ψ hψ)
  · intro ψ hψ
    have hdata := h.2.1 (sourceWeightedPeriodOne ψ) (hE hψ)
    rw [sourceAdaptedClosingMap_sub_source,norm_sourceResonantCenterRemainder]
    exact hdata
  · intro ψ hψ
    rw [fderiv_sourceAdaptedClosingMap hp ψ N (hA ψ (hinner hψ)).differentiableAt,
      add_sub_cancel_left,hder ψ (hinner hψ)]
    exact (norm_sourceClosingTransport_le _).trans_lt
      (h.2.2.1 (sourceWeightedPeriodOne ψ) (hE hψ))
  · intro x hx y hy
    rw [fderiv_sourceAdaptedClosingMap hp y N (hA y (hsmall hy)).differentiableAt,
      fderiv_sourceAdaptedClosingMap hp x N (hA x (hsmall hx)).differentiableAt,
      add_sub_add_left_eq_sub,hder y (hsmall hy),hder x (hsmall hx),
      ← ContinuousLinearMap.comp_sub,← ContinuousLinearMap.sub_comp]
    apply (norm_sourceClosingTransport_le _).trans
    simpa only [← map_sub,norm_sourceWeightedPeriodOne] using
      h.2.2.2.2 (sourceWeightedPeriodOne x) (hE hx) (sourceWeightedPeriodOne y) (hE hy)

end NLS.ZakharovShabat
