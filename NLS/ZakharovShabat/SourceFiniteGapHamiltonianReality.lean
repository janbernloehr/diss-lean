import NLS.ZakharovShabat.SourceFiniteGapHigherActionTrace
import NLS.ZakharovShabat.SourceWeightedFiniteGapDensity

/-! # Reality of the physical finite-gap hierarchy

The proved all-order physical trace formula represents every positive
Hamiltonian by a finite sum of the actual real higher actions.
-/
noncomputable section
set_option autoImplicit false
open Complex Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every independently defined physical Hamiltonian is real at a real
finite-gap source, at every order and every finite exponent greater than one. -/
theorem sourceFiniteGapNLSHamiltonian_im_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) (k : ℕ) :
    (sourceFiniteGapNLSHamiltonian hp hp1 φ hf k).im = 0 := by
  cases k with
  | zero => rfl
  | succ k =>
    have he := sourceFiniteGap_sum_higherActions_eq_hamiltonian hp hp1 φ hf k
    have hpow : (2:ℂ)^k ≠ 0 := pow_ne_zero _ (by norm_num)
    have hv := (eq_div_iff hpow).mp he
    have hsum : (∑ n ∈ hf.toFinset, (sourceRealHigherAction hp hp1 φ n k : ℂ)).im = 0 := by simp
    have hpowim (j : ℕ) : ((2:ℂ)^j).im = 0 := by
      induction j with
      | zero => simp
      | succ j ih => simp [pow_succ,Complex.mul_im,ih]
    rw [← hv,Complex.mul_im,hsum,hpowim]
    ring

/-- A continuous scalar function on the native weighted real source is real
as soon as its actual finite-gap values are real. The topology is the full
weighted norm, at every finite source exponent greater than one. -/
theorem im_eq_zero_of_continuous_weighted_finiteGap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (f : weightedRealSourceSubmodule (p := p) w → ℂ) (hf : Continuous f)
    (hfinite : ∀ a : weightedRealSourceSubmodule (p := p) w,
      originalWeightedRealSource w a ∈ sourceFiniteGapLocus hp hp1 → (f a).im = 0)
    (a : weightedRealSourceSubmodule (p := p) w) : (f a).im = 0 := by
  choose b hb hclose using fun j : ℕ => exists_weightedRealSource_finiteGap_norm_sub_lt
    hp hp1 w a (1/((j:ℝ)+1)) (by positivity)
  have hlim : Tendsto b atTop (𝓝 a) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun j => norm_nonneg (b j-a)) (fun j => (hclose j).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hv : Tendsto (fun j => (f (b j)).im) atTop (𝓝 (f a).im) :=
    (Complex.continuous_im.tendsto (f a)).comp ((hf.tendsto a).comp hlim)
  have hz : (fun j => (f (b j)).im) = fun _ : ℕ => (0:ℝ) :=
    funext fun j => hfinite (b j) (hb j)
  rw [hz] at hv
  exact (tendsto_nhds_unique hv tendsto_const_nhds)

end NLS.ZakharovShabat
