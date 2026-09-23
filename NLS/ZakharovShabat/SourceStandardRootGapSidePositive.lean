import NLS.ZakharovShabat.SourceStandardRootAlgebra
import NLS.ComplexAnalysis.SqrtBoundaryLimits

/-!
# Standard-root boundary values on the positive half of a real gap

For any midpoint `τ`, positive real half-gap `d`, and `0 < t < 1`, the
normalized standard root has the opposite upper and lower boundary
values prescribed by the real-gap specialization of equation (2.12).
The midpoint, negative half, and complex-gap orientations require
separate branch arguments.
-/

noncomputable section
open Complex Filter Set
open scoped Topology

namespace NLS.ZakharovShabat

private def q (t ε : ℝ) : ℂ := 1 - (((t:ℂ) + (ε:ℂ)*Complex.I)^2)⁻¹

private theorem q_im (t ε : ℝ) : (q t ε).im =
    2*t*ε / Complex.normSq (((t:ℂ)+(ε:ℂ)*Complex.I)^2) := by
  simp only [q, Complex.sub_im, Complex.one_im, Complex.inv_im]
  simp [Complex.mul_im, Complex.add_im, Complex.add_re, Complex.mul_re, pow_two]
  ring

private theorem q_im_pos (t ε : ℝ) (ht : 0 < t) (hε : 0 < ε) : 0 < (q t ε).im := by
  rw [q_im]
  apply div_pos
  · positivity
  · apply Complex.normSq_pos.mpr
    apply pow_ne_zero
    intro he
    have hre := congrArg Complex.re he
    have htzero : t = 0 := by simpa using hre
    exact (ne_of_gt ht) htzero

private theorem q_tendsto (t : ℝ) (ht : 0 < t) :
    Tendsto (q t) (𝓝[>] (0:ℝ))
      (𝓝[{z : ℂ | 0 < z.im}] (-((t⁻¹^2-1:ℝ):ℂ))) := by
  have hcont : ContinuousAt (q t) 0 := by
    unfold q
    fun_prop (disch :=
      have htne : (t:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht
      simp [htne])
  have hvalue : q t 0 = -((t⁻¹^2-1:ℝ):ℂ) := by
    simp [q, inv_pow]
  rw [← hvalue]
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact q_im_pos t ε ht hε

private theorem q_sqrt_tendsto (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    Tendsto (fun ε : ℝ => Complex.sqrt (q t ε)) (𝓝[>] (0:ℝ))
      (𝓝 (Complex.I * (Real.sqrt (t⁻¹^2-1) : ℂ))) := by
  have hr : 0 ≤ t⁻¹^2-1 := by
    have hti : 1 < t⁻¹ := one_lt_inv_iff₀.mpr ⟨ht, ht1⟩
    nlinarith
  exact (NLS.ComplexAnalysis.sqrt_tendsto_neg_real_upper _ hr).comp
    (q_tendsto t ht)

private theorem root_eq (τ : ℂ) (d t ε : ℝ) (hd : 0 < d) (ht : 0 < t) :
    NLS.ZakharovShabat.normalizedStandardRoot τ ((2*(d:ℂ))^2)
      (τ+(d:ℂ)*((t:ℂ)+(ε:ℂ)*I)) =
    -(d:ℂ)*((t:ℂ)+(ε:ℂ)*I)*Complex.sqrt (q t ε) := by
  let u : ℂ := (t:ℂ)+(ε:ℂ)*I
  have hu : u ≠ 0 := by
    intro he
    have hre := congrArg Complex.re he
    have htzero : t = 0 := by simpa [u] using hre
    exact (ne_of_gt ht) htzero
  have hdC : (d:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hd
  have hfactor : τ - (τ + (d:ℂ)*u) = -(d:ℂ)*u := by ring
  have hrad : 1 - (2*(d:ℂ))^2/(4*(τ-(τ+(d:ℂ)*u))^2) =
      1-(u^2)⁻¹ := by
    rw [hfactor]
    field_simp
    ring
  unfold NLS.ZakharovShabat.normalizedStandardRoot
  change (τ - (τ + (d:ℂ)*u)) *
      Complex.sqrt (1-(2*(d:ℂ))^2/(4*(τ-(τ+(d:ℂ)*u))^2)) =
    -(d:ℂ)*u*Complex.sqrt (q t ε)
  rw [hrad, hfactor]
  rfl

private theorem sqrt_gap_identity (t : ℝ) (ht : 0 < t) :
    t * Real.sqrt (t⁻¹^2-1) = Real.sqrt (1-t^2) := by
  have hsq : t^2*(t⁻¹^2-1) = 1-t^2 := by
    have hne : t ≠ 0 := ne_of_gt ht
    field_simp
  calc
    t * Real.sqrt (t⁻¹^2-1) = Real.sqrt (t^2)*Real.sqrt (t⁻¹^2-1) := by
      rw [Real.sqrt_sq ht.le]
    _ = Real.sqrt (t^2*(t⁻¹^2-1)) := (Real.sqrt_mul (sq_nonneg t) _).symm
    _ = Real.sqrt (1-t^2) := by rw [hsq]

/-- Equation (2.12) on the positive half of a gap, approached from above. -/
theorem normalizedStandardRoot_tendsto_gap_upper_pos (τ : ℂ) (d t : ℝ)
    (hd : 0 < d) (ht : 0 < t) (ht1 : t < 1) :
    Tendsto (fun ε : ℝ =>
      NLS.ZakharovShabat.normalizedStandardRoot τ ((2*(d:ℂ))^2)
        (τ+(d:ℂ)*((t:ℂ)+(ε:ℂ)*I)))
      (𝓝[>] (0:ℝ))
      (𝓝 (-(d:ℂ)*I*(Real.sqrt (1-t^2):ℂ))) := by
  have hlin : Tendsto (fun ε : ℝ =>
      -(d:ℂ)*((t:ℂ)+(ε:ℂ)*I)) (𝓝[>] (0:ℝ))
      (𝓝 (-(d:ℂ)*(t:ℂ))) := by
    have hc : ContinuousAt (fun ε : ℝ =>
      -(d:ℂ)*((t:ℂ)+(ε:ℂ)*I)) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hmul := hlin.mul (q_sqrt_tendsto t ht ht1)
  have hlim : Tendsto (fun ε : ℝ =>
      -(d:ℂ)*((t:ℂ)+(ε:ℂ)*I)*Complex.sqrt (q t ε))
      (𝓝[>] (0:ℝ))
      (𝓝 (-(d:ℂ)*(t:ℂ)*(I*(Real.sqrt (t⁻¹^2-1):ℂ)))) := hmul
  have hval : -(d:ℂ)*(t:ℂ)*(I*(Real.sqrt (t⁻¹^2-1):ℂ)) =
      -(d:ℂ)*I*(Real.sqrt (1-t^2):ℂ) := by
    rw [← sqrt_gap_identity t ht]
    push_cast
    ring
  rw [← hval]
  exact hlim.congr' (Filter.Eventually.of_forall fun ε =>
    (root_eq τ d t ε hd ht).symm)

private theorem q_sqrt_tendsto_lower (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    Tendsto (fun ε : ℝ => Complex.sqrt (q t (-ε))) (𝓝[>] (0:ℝ))
      (𝓝 (-I * (Real.sqrt (t⁻¹^2-1) : ℂ))) := by
  have hr : 0 ≤ t⁻¹^2-1 := by
    have hti : 1 < t⁻¹ := one_lt_inv_iff₀.mpr ⟨ht, ht1⟩
    nlinarith
  have hcont : ContinuousAt (fun ε : ℝ => q t (-ε)) 0 := by
    unfold q
    fun_prop (disch :=
      have htne : (t:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht
      simp [htne])
  have hvalue : q t (-0) = -((t⁻¹^2-1:ℝ):ℂ) := by
    simp [q, inv_pow]
  have hq : Tendsto (fun ε : ℝ => q t (-ε)) (𝓝[>] (0:ℝ))
      (𝓝[{z : ℂ | z.im < 0}] (-((t⁻¹^2-1:ℝ):ℂ))) := by
    rw [← hvalue]
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact hcont.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      change 0 < ε at hε
      rw [q_im]
      have hden : 0 < Complex.normSq (((t:ℂ)+((-ε:ℝ):ℂ)*I)^2) := by
        apply Complex.normSq_pos.mpr
        apply pow_ne_zero
        intro he
        have hre := congrArg Complex.re he
        have htzero : t = 0 := by simpa using hre
        exact (ne_of_gt ht) htzero
      exact div_neg_of_neg_of_pos (by nlinarith) hden
  exact (NLS.ComplexAnalysis.sqrt_tendsto_neg_real_lower _ hr).comp hq

/-- Equation (2.12) on the positive half of a gap, approached from below. -/
theorem normalizedStandardRoot_tendsto_gap_lower_pos (τ : ℂ) (d t : ℝ)
    (hd : 0 < d) (ht : 0 < t) (ht1 : t < 1) :
    Tendsto (fun ε : ℝ =>
      NLS.ZakharovShabat.normalizedStandardRoot τ ((2*(d:ℂ))^2)
        (τ+(d:ℂ)*((t:ℂ)-(ε:ℂ)*I)))
      (𝓝[>] (0:ℝ))
      (𝓝 ((d:ℂ)*I*(Real.sqrt (1-t^2):ℂ))) := by
  have hlin : Tendsto (fun ε : ℝ =>
      -(d:ℂ)*((t:ℂ)+((-ε:ℝ):ℂ)*I)) (𝓝[>] (0:ℝ))
      (𝓝 (-(d:ℂ)*(t:ℂ))) := by
    have hc : ContinuousAt (fun ε : ℝ =>
      -(d:ℂ)*((t:ℂ)+((-ε:ℝ):ℂ)*I)) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hmul := hlin.mul (q_sqrt_tendsto_lower t ht ht1)
  have hlim : Tendsto (fun ε : ℝ =>
      -(d:ℂ)*((t:ℂ)+((-ε:ℝ):ℂ)*I)*Complex.sqrt (q t (-ε)))
      (𝓝[>] (0:ℝ))
      (𝓝 (-(d:ℂ)*(t:ℂ)*(-I*(Real.sqrt (t⁻¹^2-1):ℂ)))) := hmul
  have hval : -(d:ℂ)*(t:ℂ)*(-I*(Real.sqrt (t⁻¹^2-1):ℂ)) =
      (d:ℂ)*I*(Real.sqrt (1-t^2):ℂ) := by
    rw [← sqrt_gap_identity t ht]
    push_cast
    ring
  rw [← hval]
  have hlim' := hlim.congr' (Filter.Eventually.of_forall fun ε =>
    (root_eq τ d t (-ε) hd ht).symm)
  convert hlim' using 1
  ext ε
  congr 1
  push_cast
  ring

end NLS.ZakharovShabat
