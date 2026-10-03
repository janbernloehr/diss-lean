import NLS.ZakharovShabat.ContourTraceCoefficientConvergence
import NLS.ZakharovShabat.SpectralClusterCoefficientStability
import NLS.ZakharovShabat.SymmetricEigenvalues

/-! # Convergence of ordered real eigenvalue pairs

A circle isolating a real rank-two cluster determines both endpoints from
its midpoint and squared gap. The square root is continuous also at zero,
so bounded coefficient limits preserve each ordered endpoint, even when
an open gap collapses. Identification with a global index is a separate input.
-/
noncomputable section
open Set Filter Topology Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Recover the ordered real endpoints of a rank-two contour from its two
symmetric trace expressions, allowing a repeated eigenvalue. -/
theorem contour_real_pair_reconstruction (hp : p ≠ ⊤) (φ : PairSpace p)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ)
    (hdim : Module.finrank ℂ (resolventCircleIntegral hp φ c r).range = 2)
    (a b : ℝ) (hab : a ≤ b)
    (hs : enclosedPeriodicSpectrum hp φ c r = {(a : ℂ), (b : ℂ)}) :
    (contourMidpoint hp φ c r).re - Real.sqrt (contourSquaredGap hp φ c r).re / 2 = a ∧
      (contourMidpoint hp φ c r).re + Real.sqrt (contourSquaredGap hp φ c r).re / 2 = b := by
  have h := contourMidpoint_squaredGap_eq_pair hp φ c r hr hc hdim a b hs
  have hm : (contourMidpoint hp φ c r).re = (a+b)/2 := by rw [h.1]; simp
  have hg : (contourSquaredGap hp φ c r).re = (a-b)^2 := by
    rw [h.2.1, ← Complex.ofReal_sub, ← Complex.ofReal_pow, Complex.ofReal_re]
  rw [hm, hg, Real.sqrt_sq_eq_abs, abs_of_nonpos (sub_nonpos.mpr hab)]
  constructor <;> ring

/-- Any consistently ordered real pair exhausting the varying rank-two
cluster converges endpoint by endpoint under bounded coefficient limits.
Only eventual pair identification is needed; rank stability is proved. -/
theorem tendsto_real_spectral_pair_of_bounded_coefficientwise
    (hp : p ≠ ⊤) (hp1 : 1 < p) {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (φ : α → PairSpace p) (ψ : PairSpace p) (hb : Bornology.IsBounded (range φ))
    (ht₁ : ∀ n : ℤ, Tendsto (fun k => (φ k).1 n) l (𝓝 (ψ.1 n)))
    (ht₂ : ∀ n : ℤ, Tendsto (fun k => (φ k).2 n) l (𝓝 (ψ.2 n)))
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp ψ)
    (hdim : Module.finrank ℂ (resolventCircleIntegral hp ψ c r).range = 2)
    (a b : α → ℝ) (x y : ℝ) (hxy : x ≤ y)
    (hψ : enclosedPeriodicSpectrum hp ψ c r = {(x : ℂ), (y : ℂ)})
    (hab : ∀ᶠ k in l, a k ≤ b k ∧
      enclosedPeriodicSpectrum hp (φ k) c r = {(a k : ℂ), (b k : ℂ)}) :
    Tendsto a l (𝓝 x) ∧ Tendsto b l (𝓝 y) := by
  have h := tendsto_contourMidpoint_and_squaredGap_of_bounded_coefficientwise hp hp1 φ ψ hb ht₁ ht₂ c r hr hc
  have hm := Complex.continuous_re.continuousAt.tendsto.comp h.1
  have hg := Real.continuous_sqrt.continuousAt.tendsto.comp
    (Complex.continuous_re.continuousAt.tendsto.comp h.2)
  have hx := hm.sub (hg.div_const 2)
  have hy := hm.add (hg.div_const 2)
  have hlim := contour_real_pair_reconstruction hp ψ c r hr hc hdim x y hxy hψ
  rw [hlim.1] at hx
  rw [hlim.2] at hy
  have he : ∀ᶠ k in l,
      (contourMidpoint hp (φ k) c r).re - Real.sqrt (contourSquaredGap hp (φ k) c r).re / 2 = a k ∧
      (contourMidpoint hp (φ k) c r).re + Real.sqrt (contourSquaredGap hp (φ k) c r).re / 2 = b k := by
    filter_upwards [hab, eventually_finrank_resolventCircleIntegral_eq_of_bounded_coefficientwise
      hp hp1 φ ψ hb ht₁ ht₂ c r hr hc] with k hk hrank
    exact contour_real_pair_reconstruction hp (φ k) c r hr hrank.1
      (hrank.2.trans hdim) (a k) (b k) hk.1 hk.2
  exact ⟨hx.congr' (he.mono fun _ hk => hk.1), hy.congr' (he.mono fun _ hk => hk.2)⟩

/-- At a zero coefficient limit every fixed free spectral disk has midpoint
limit `π n` and squared-gap limit zero. No eigenvalue labeling is assumed. -/
theorem tendsto_periodicMidpoint_and_squaredGap_zero_of_bounded_coefficientwise
    (hp : p ≠ ⊤) (hp1 : 1 < p) {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (φ : α → PairSpace p) (hb : Bornology.IsBounded (range φ))
    (ht₁ : ∀ n : ℤ, Tendsto (fun k => (φ k).1 n) l (𝓝 0))
    (ht₂ : ∀ n : ℤ, Tendsto (fun k => (φ k).2 n) l (𝓝 0)) (n : ℤ) :
    Tendsto (fun k => periodicMidpoint hp (φ k) n) l (𝓝 ((Real.pi : ℂ)*n)) ∧
      Tendsto (fun k => periodicSquaredGap hp (φ k) n) l (𝓝 0) := by
  have hr : 0 < Real.pi / 4 := by positivity
  have hc := sphere_subset_resolventSet_of_smallPotential (p := p) hp 0 n hr le_rfl (by simpa using hr)
  have h := tendsto_contourMidpoint_and_squaredGap_of_bounded_coefficientwise hp hp1 φ 0 hb ht₁ ht₂
    ((Real.pi : ℂ)*n) (Real.pi/4) hr.le hc
  change Tendsto (fun k => periodicMidpoint hp (φ k) n) l (𝓝 (periodicMidpoint hp 0 n)) ∧
    Tendsto (fun k => periodicSquaredGap hp (φ k) n) l (𝓝 (periodicSquaredGap hp 0 n)) at h
  simpa only [(periodicMidpoint_squaredGap_zero hp n).1, (periodicMidpoint_squaredGap_zero hp n).2] using h

end NLS.ZakharovShabat
