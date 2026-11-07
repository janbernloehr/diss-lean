import NLS.SequenceSpaces.CompactGaugeDerivative
import NLS.SequenceSpaces.CompactUnitSymbolDerivative

/-! Removing an analytic bounded exponent with vanishing signed
tails changes the actual weighted derivative by a compact operator.
The principal linear map is unchanged. -/
noncomputable section
open Complex Set Metric Filter Topology
open scoped ENNReal
namespace NLS.Coeff

theorem infty_exp_unit_tail (b : Coeff ⊤)
    (ht : ∀ ε > (0:ℝ), ∃ K : ℕ, ∀ k : ℤ, K ≤ k.natAbs → ‖b k‖ ≤ ε) :
    ∀ ε > (0:ℝ), ∃ K : ℕ, ∀ k : ℤ, K ≤ k.natAbs →
      ‖NormedSpace.exp b k-1‖ ≤ ε := by
  intro ε hε
  obtain ⟨δ,hδ,hb⟩ := Metric.mem_nhds_iff.mp
    (Complex.continuous_exp.continuousAt (ball_mem_nhds (Complex.exp 0) hε))
  obtain ⟨K,hK⟩ := ht (δ/2) (half_pos hδ)
  refine ⟨K,?_⟩
  intro k hk
  have hnear : b k ∈ ball (0:ℂ) δ := by
    rw [mem_ball,dist_zero_right]
    exact (hK k hk).trans_lt (half_lt_self hδ)
  have he := hb hnear
  rw [infty_exp_apply]
  exact (show ‖Complex.exp (b k)-1‖ < ε by
    simpa only [mem_preimage,mem_ball,dist_eq_norm,Complex.exp_zero] using he).le

end NLS.Coeff
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem isCompactOperator_removeZeroTailExponentialSymbol_difference (w : Weight) (hp : p ≠ ⊤)
    (θ : E → Coeff ⊤) (f : E → WeightedCoeff w p) (q : E)
    (hθ : AnalyticAt ℂ θ q) (hf : AnalyticAt ℂ f q)
    (ht : ∀ ε > (0:ℝ), ∃ K : ℕ, ∀ k : ℤ, K ≤ k.natAbs → ‖θ q k‖ ≤ ε) :
    IsCompactOperator (fderiv ℂ f q-fderiv ℂ (removeExponentialSymbol w θ f) q) := by
  let g := removeExponentialSymbol w θ f
  have he : f = fun x => boundedSymbolBilinear w (NormedSpace.exp (θ x)) (g x) := by
    funext x
    exact ((exponentialSymbolEquiv w (θ x)).apply_symm_apply (f x)).symm
  have hd : fderiv ℂ f q = fderiv ℂ (fun x => boundedSymbolBilinear w (NormedSpace.exp (θ x)) (g x)) q :=
    congrArg (fun F => fderiv ℂ F q) he
  rw [hd]
  exact isCompactOperator_fderiv_boundedSymbol_sub w hp (fun x => NormedSpace.exp (θ x)) g q
    ((NormedSpace.exp_analytic _).comp hθ)
    (analyticAt_removeExponentialSymbol w θ f q hθ hf) (Coeff.infty_exp_unit_tail (θ q) ht)

end NLS.WeightedCoeff
