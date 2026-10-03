import NLS.ZakharovShabat.RealSpectralPairCoefficientConvergence

/-! # Spectral trace and ordered-pair limits for period-one sources

Bounded coefficientwise source limits give convergence of every finite
spectral power trace and of the rank-two symmetric trace expressions.
A specified ordered real eigenvalue pair converges whenever it eventually
exhausts the same isolating circle.
-/
noncomputable section
open Set Filter Topology Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem bounded_periodOnePotential_range {α : Type*}
    (φ : α → CoeffPair p) (hb : Bornology.IsBounded (range φ)) :
    Bornology.IsBounded (range (fun k => periodOnePotential (φ k))) := by
  obtain ⟨M, hM⟩ := hb.exists_norm_le
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨M, ?_⟩
  rintro _ ⟨k, rfl⟩
  exact (norm_periodOnePotential_le (φ k)).trans (hM _ ⟨k, rfl⟩)

/-- The bounded contour restrictions converge for bounded source coefficient limits. -/
theorem tendsto_source_contourOperator_of_bounded_coefficientwise
    (hp : p ≠ ⊤) (hp1 : 1 < p) {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (φ : α → CoeffPair p) (ψ : CoeffPair p) (hb : Bornology.IsBounded (range φ))
    (ht₁ : ∀ n : ℤ, Tendsto (fun k => (φ k).fst n) l (𝓝 (ψ.fst n)))
    (ht₂ : ∀ n : ℤ, Tendsto (fun k => (φ k).snd n) l (𝓝 (ψ.snd n)))
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp (periodOnePotential ψ)) :
    Tendsto (fun k => contourOperator hp (periodOnePotential (φ k)) c r) l (𝓝 (contourOperator hp (periodOnePotential ψ) c r)) := by
  exact tendsto_contourOperator_of_bounded_coefficientwise hp hp1
    (fun k => periodOnePotential (φ k)) (periodOnePotential ψ)
    (bounded_periodOnePotential_range φ hb)
    (tendsto_periodDouble_coefficientwise (fun k => (φ k).fst) ψ.fst ht₁)
    (tendsto_periodDouble_coefficientwise (fun k => (φ k).snd) ψ.snd ht₂) c r hr hc

/-- Every intrinsic contour power trace converges in period-one source coordinates. -/
theorem tendsto_source_contourTracePower_of_bounded_coefficientwise
    (hp : p ≠ ⊤) (hp1 : 1 < p) {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (φ : α → CoeffPair p) (ψ : CoeffPair p) (hb : Bornology.IsBounded (range φ))
    (ht₁ : ∀ n : ℤ, Tendsto (fun k => (φ k).fst n) l (𝓝 (ψ.fst n)))
    (ht₂ : ∀ n : ℤ, Tendsto (fun k => (φ k).snd n) l (𝓝 (ψ.snd n)))
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp (periodOnePotential ψ)) (m : ℕ) :
    Tendsto (fun k => contourTracePower hp (periodOnePotential (φ k)) c r m) l
      (𝓝 (contourTracePower hp (periodOnePotential ψ) c r m)) := by
  exact tendsto_contourTracePower_of_bounded_coefficientwise hp hp1
    (fun k => periodOnePotential (φ k)) (periodOnePotential ψ)
    (bounded_periodOnePotential_range φ hb)
    (tendsto_periodDouble_coefficientwise (fun k => (φ k).fst) ψ.fst ht₁)
    (tendsto_periodDouble_coefficientwise (fun k => (φ k).snd) ψ.snd ht₂) c r hr hc m

/-- Both contour symmetric trace expressions converge for bounded source coefficient limits. -/
theorem tendsto_source_contourMidpoint_and_squaredGap_of_bounded_coefficientwise
    (hp : p ≠ ⊤) (hp1 : 1 < p) {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (φ : α → CoeffPair p) (ψ : CoeffPair p) (hb : Bornology.IsBounded (range φ))
    (ht₁ : ∀ n : ℤ, Tendsto (fun k => (φ k).fst n) l (𝓝 (ψ.fst n)))
    (ht₂ : ∀ n : ℤ, Tendsto (fun k => (φ k).snd n) l (𝓝 (ψ.snd n)))
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp (periodOnePotential ψ)) :
    Tendsto (fun k => contourMidpoint hp (periodOnePotential (φ k)) c r) l (𝓝 (contourMidpoint hp (periodOnePotential ψ) c r)) ∧
      Tendsto (fun k => contourSquaredGap hp (periodOnePotential (φ k)) c r) l (𝓝 (contourSquaredGap hp (periodOnePotential ψ) c r)) := by
  exact tendsto_contourMidpoint_and_squaredGap_of_bounded_coefficientwise hp hp1
    (fun k => periodOnePotential (φ k)) (periodOnePotential ψ)
    (bounded_periodOnePotential_range φ hb)
    (tendsto_periodDouble_coefficientwise (fun k => (φ k).fst) ψ.fst ht₁)
    (tendsto_periodDouble_coefficientwise (fun k => (φ k).snd) ψ.snd ht₂) c r hr hc

/-- Ordered real source spectral pairs converge on a fixed isolating circle, including at a double root. -/
theorem tendsto_source_real_spectral_pair_of_bounded_coefficientwise
    (hp : p ≠ ⊤) (hp1 : 1 < p) {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (φ : α → CoeffPair p) (ψ : CoeffPair p) (hb : Bornology.IsBounded (range φ))
    (ht₁ : ∀ n : ℤ, Tendsto (fun k => (φ k).fst n) l (𝓝 (ψ.fst n)))
    (ht₂ : ∀ n : ℤ, Tendsto (fun k => (φ k).snd n) l (𝓝 (ψ.snd n)))
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp (periodOnePotential ψ))
    (hdim : Module.finrank ℂ (resolventCircleIntegral hp (periodOnePotential ψ) c r).range = 2)
    (a b : α → ℝ) (x y : ℝ) (hxy : x ≤ y)
    (hψ : enclosedPeriodicSpectrum hp (periodOnePotential ψ) c r = {(x : ℂ), (y : ℂ)})
    (hab : ∀ᶠ k in l, a k ≤ b k ∧
      enclosedPeriodicSpectrum hp (periodOnePotential (φ k)) c r = {(a k : ℂ), (b k : ℂ)}) :
    Tendsto a l (𝓝 x) ∧ Tendsto b l (𝓝 y) := by
  exact tendsto_real_spectral_pair_of_bounded_coefficientwise hp hp1
    (fun k => periodOnePotential (φ k)) (periodOnePotential ψ)
    (bounded_periodOnePotential_range φ hb)
    (tendsto_periodDouble_coefficientwise (fun k => (φ k).fst) ψ.fst ht₁)
    (tendsto_periodDouble_coefficientwise (fun k => (φ k).snd) ψ.snd ht₂) c r hr hc hdim a b x y hxy hψ hab

end NLS.ZakharovShabat
