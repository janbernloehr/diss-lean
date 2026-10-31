import NLS.ZakharovShabat.SourceStandardRootAnalytic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # The standard root on the midpoint paths in Appendix F -/
noncomputable section
open Complex Filter Topology
open scoped ComplexOrder
namespace NLS.ComplexAnalysis

/-- Positive real rescaling preserves the principal square-root branch. -/
theorem appendixF_sqrt_positive_scale (t : ℝ) (ht : 0 < t) (z : ℂ) :
    Complex.sqrt ((t : ℂ)^2*z) = (t : ℂ)*Complex.sqrt z := by
  by_cases hz : z = 0
  · simp [hz]
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hsq : Complex.sqrt ((t : ℂ)^2) = (t : ℂ) := by
    rw [← Complex.ofReal_pow, Complex.sqrt_of_nonneg (by exact_mod_cast sq_nonneg t)]
    simp only [Complex.ofReal_re, Real.sqrt_sq ht.le]
  calc
    Complex.sqrt ((t : ℂ)^2*z) = Complex.sqrt ((t : ℂ)^2)*Complex.sqrt z := by
      simp only [Complex.sqrt, Complex.cpow_def_of_ne_zero
        (mul_ne_zero (pow_ne_zero 2 htC) hz),
        Complex.cpow_def_of_ne_zero (pow_ne_zero 2 htC), Complex.cpow_def_of_ne_zero hz]
      rw [← Complex.ofReal_pow, Complex.log_ofReal_mul (sq_pos_of_pos ht) hz,
        Complex.ofReal_log (sq_nonneg t), add_mul, Complex.exp_add]
    _ = (t : ℂ)*Complex.sqrt z := by rw [hsq]

end NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

/-- On a positive midpoint ray the actual normalized root has the printed rescaled
principal-root expression; the terminal displacement is allowed to be complex. -/
theorem appendixF_normalized_root_on_spoke (τ γ z : ℂ) (hz : z ≠ 0)
    (t : ℝ) (ht : 0 < t) :
    normalizedStandardRoot τ (γ^2) (τ+(t:ℂ)*z) =
      -z * Complex.sqrt ((t:ℂ)^2-(γ/(2*z))^2) := by
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hlin : τ-(τ+(t:ℂ)*z) = -(t:ℂ)*z := by ring
  have hrad : (t:ℂ)^2-(γ/(2*z))^2 =
      (t:ℂ)^2*(1-γ^2/(4*(-(t:ℂ)*z)^2)) := by
    field_simp
    ring
  rw [normalizedStandardRoot, hlin, hrad,
    NLS.ComplexAnalysis.appendixF_sqrt_positive_scale t ht]
  ring

/-- At every positive path parameter, a collapsing gap gives the linear standard-root
limit. No statement about the singular path endpoint is needed. -/
theorem appendixF_normalized_root_spoke_tendsto {ι : Type*} {l : Filter ι}
    (τ γ z : ι → ℂ) (z₀ : ℂ) (hz₀ : z₀ ≠ 0)
    (hγ : Tendsto γ l (𝓝 0)) (hz : Tendsto z l (𝓝 z₀))
    (t : ℝ) (ht : 0 < t) :
    Tendsto (fun k => normalizedStandardRoot (τ k) ((γ k)^2) (τ k+(t:ℂ)*z k))
      l (𝓝 (-(t:ℂ)*z₀)) := by
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hlin : Tendsto (fun k => (τ k)-(τ k+(t:ℂ)*z k)) l (𝓝 (-(t:ℂ)*z₀)) := by
    convert (tendsto_const_nhds.mul hz : Tendsto (fun k => -(t:ℂ)*z k) l
      (𝓝 (-(t:ℂ)*z₀))) using 1
    ext k
    ring
  have hd : (4:ℂ)*(-(t:ℂ)*z₀)^2 ≠ 0 := by
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (mul_ne_zero (neg_ne_zero.mpr htC) hz₀))
  have hrad : Tendsto (fun k => 1-(γ k)^2/(4*((τ k)-(τ k+(t:ℂ)*z k))^2))
      l (𝓝 (1:ℂ)) := by
    simpa using tendsto_const_nhds.sub ((hγ.pow 2).div (tendsto_const_nhds.mul (hlin.pow 2)) hd)
  have hs := (Complex.continuousAt_sqrt (z := 1) (Or.inl (by norm_num))).tendsto.comp hrad
  simpa only [normalizedStandardRoot, Function.comp_apply, Pi.mul_apply,
    Complex.sqrt_one, mul_one] using hlin.mul hs

/-- The actual differential quotient converges to one at each positive path parameter
when the critical point and midpoint coalesce and the gap collapses. -/
theorem appendixF_spoke_quotient_tendsto {ι : Type*} {l : Filter ι}
    (τ γ a z : ι → ℂ) (z₀ : ℂ) (hz₀ : z₀ ≠ 0)
    (hγ : Tendsto γ l (𝓝 0)) (hz : Tendsto z l (𝓝 z₀))
    (ha : Tendsto (fun k => a k-τ k) l (𝓝 0)) (t : ℝ) (ht : 0 < t) :
    Tendsto (fun k => (a k-(τ k+(t:ℂ)*z k)) /
      normalizedStandardRoot (τ k) ((γ k)^2) (τ k+(t:ℂ)*z k)) l (𝓝 1) := by
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hn : Tendsto (fun k => a k-(τ k+(t:ℂ)*z k)) l (𝓝 (-(t:ℂ)*z₀)) := by
    have hh := ha.sub (tendsto_const_nhds.mul hz :
      Tendsto (fun k => (t:ℂ)*z k) l (𝓝 ((t:ℂ)*z₀)))
    simpa only [Pi.sub_apply, zero_sub, sub_add_eq_sub_sub, neg_mul] using hh
  have hd := appendixF_normalized_root_spoke_tendsto τ γ z z₀ hz₀ hγ hz t ht
  convert hn.div hd (mul_ne_zero (neg_ne_zero.mpr htC) hz₀) using 1
  · rfl
  · rw [div_self (mul_ne_zero (neg_ne_zero.mpr htC) hz₀)]

/-- Joint continuity of the regular factor gives the limit of the actual rescaled
midpoint-path integrand, with both the spectral point and source allowed to move. -/
theorem appendixF_spoke_integrand_tendsto {ι X : Type*} [TopologicalSpace X]
    {l : Filter ι} (τ γ a z : ι → ℂ) (ψ : ι → X) (τ₀ z₀ : ℂ) (ψ₀ : X)
    (hz₀ : z₀ ≠ 0) (hτ : Tendsto τ l (𝓝 τ₀)) (hγ : Tendsto γ l (𝓝 0))
    (hz : Tendsto z l (𝓝 z₀)) (hψ : Tendsto ψ l (𝓝 ψ₀))
    (ha : Tendsto (fun k => a k-τ k) l (𝓝 0)) (t : ℝ) (ht : 0 < t)
    (χ : ℂ × X → ℂ) (hχ : ContinuousAt χ (τ₀+(t:ℂ)*z₀, ψ₀)) :
    Tendsto (fun k => z k * ((a k-(τ k+(t:ℂ)*z k)) /
      normalizedStandardRoot (τ k) ((γ k)^2) (τ k+(t:ℂ)*z k)) *
      χ (τ k+(t:ℂ)*z k, ψ k)) l (𝓝 (z₀*χ (τ₀+(t:ℂ)*z₀, ψ₀))) := by
  have hpoint : Tendsto (fun k => (τ k+(t:ℂ)*z k, ψ k)) l
      (𝓝 (τ₀+(t:ℂ)*z₀, ψ₀)) :=
    (hτ.add (tendsto_const_nhds.mul hz)).prodMk_nhds hψ
  have hregular := hχ.tendsto.comp hpoint
  have hquot := appendixF_spoke_quotient_tendsto τ γ a z z₀ hz₀ hγ hz ha t ht
  convert (hz.mul hquot).mul hregular using 1
  · rfl
  · simp only [mul_one]

end NLS.ZakharovShabat
