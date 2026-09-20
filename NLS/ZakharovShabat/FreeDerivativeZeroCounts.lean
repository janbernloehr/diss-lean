import NLS.ZakharovShabat.DiscriminantCriticalLocalization
import NLS.ZakharovShabat.CentralDeformation
import NLS.ComplexAnalysis.IsolatedOrderStability

/-!
# Exact zero counts for the free discriminant derivative

Every free critical point has analytic order one. A disc of radius less than
pi about a free center contains just that zero; the central circle of radius
(N+1/2)pi contains precisely the 2N+1 centers with indices from -N to N.
-/

noncomputable section
open Set Complex Metric
open NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

/-- Distance between two free lattice centers. -/
theorem norm_free_center_sub (n m : ℤ) :
    ‖(Real.pi : ℂ)*n-(Real.pi : ℂ)*m‖ = Real.pi*|((n-m : ℤ) : ℝ)| := by
  rw [← mul_sub, norm_mul]
  simp only [← Int.cast_sub, Complex.norm_intCast, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]

/-- A free lattice point is inside the central closed disc exactly at a central index. -/
theorem free_center_mem_closedCentralCircle_iff (N : ℕ) (n : ℤ) :
    (Real.pi : ℂ)*n ∈ closedBall 0 (centralCircleRadius N) ↔ n.natAbs ≤ N := by
  have he : ‖(Real.pi : ℂ)*n‖ = Real.pi*(n.natAbs : ℝ) := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      Complex.norm_intCast, Nat.cast_natAbs, Int.cast_abs]
  rw [mem_closedBall, dist_zero_right, he]
  unfold centralCircleRadius
  constructor
  · intro h
    have hlt : (n.natAbs : ℝ) < (N : ℝ)+1 := by nlinarith [Real.pi_pos]
    have hn : n.natAbs < N+1 := by exact_mod_cast hlt
    omega
  · intro h
    have hn : (n.natAbs : ℝ) ≤ (N : ℝ) := by exact_mod_cast h
    nlinarith [Real.pi_pos]

/-- Each zero of the free derivative is simple. -/
theorem analyticOrderAt_free_derivative (n : ℤ) :
    analyticOrderAt (fun z : ℂ => -2*sin z) ((Real.pi : ℂ)*n) = 1 := by
  have hs : sin ((Real.pi : ℂ)*n) = 0 := by
    rw [mul_comm]; exact Complex.sin_int_mul_pi n
  have hc : cos ((Real.pi : ℂ)*n) ≠ 0 := by
    intro h
    have he := Complex.sin_sq_add_cos_sq ((Real.pi : ℂ)*n)
    simp only [hs, h, zero_pow (by decide : 2 ≠ 0), zero_add] at he
    exact zero_ne_one he
  apply AnalyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero (by fun_prop)
  · rw [hs, mul_zero]
  · rw [((Complex.hasDerivAt_sin _).const_mul (-2)).deriv]
    exact mul_ne_zero (by norm_num) hc

/-- No other free critical point lies in a disc of radius less than pi. -/
theorem free_derivative_zero_eq_center {r : ℝ} (hr : r < Real.pi) (n : ℤ)
    {z : ℂ} (hz : z ∈ closedBall ((Real.pi : ℂ)*n) r) (hzero : -2*sin z = 0) :
    z = (Real.pi : ℂ)*n := by
  have hs : sin z = 0 := (mul_eq_zero.mp hzero).resolve_left (by norm_num)
  obtain ⟨m, hm⟩ := Complex.sin_eq_zero_iff.mp hs
  have he : z = (Real.pi : ℂ)*m := hm.trans (mul_comm _ _)
  rw [he, mem_closedBall, dist_eq_norm, norm_free_center_sub] at hz
  have hmn : m = n := by
    by_contra h
    have ha : (1 : ℝ) ≤ |((m-n : ℤ) : ℝ)| := by
      exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr h)
    nlinarith [Real.pi_pos]
  simpa only [hmn] using he

/-- The free derivative has count one in each sufficiently small free disc. -/
theorem analyticZeroCount_free_derivative_disc {r : ℝ} (hr : 0 ≤ r) (hrπ : r < Real.pi) (n : ℤ) :
    analyticZeroCount (fun z : ℂ => -2*sin z) (closedBall ((Real.pi : ℂ)*n) r) = 1 := by
  rw [analyticZeroCount_eq_order_of_isolated _ _ _ hr
    (fun _ hz hzero => free_derivative_zero_eq_center hrπ n hz hzero)]
  simp only [analyticOrderNatAt, analyticOrderAt_free_derivative, ENat.toNat_one]

/-- The central free derivative count is exactly 2N+1, including the zero mode. -/
theorem analyticZeroCount_free_derivative_central (N : ℕ) :
    analyticZeroCount (fun z : ℂ => -2*sin z) (closedBall 0 (centralCircleRadius N)) = 2*N+1 := by
  classical
  let s := (Finset.Icc (-(N : ℤ)) N).image (fun n : ℤ => (Real.pi : ℂ)*n)
  rw [analyticZeroCount_eq_sum s]
  · rw [Finset.sum_image]
    · simp only [analyticOrderNatAt, analyticOrderAt_free_derivative, ENat.toNat_one,
        Finset.sum_const, smul_eq_mul, Int.card_Icc, mul_one]
      omega
    · intro a _ b _ h
      have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      exact_mod_cast mul_left_cancel₀ hπ h
  · intro z hz
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hz
    apply (free_center_mem_closedCentralCircle_iff N n).mpr
    rw [Finset.mem_Icc] at hn
    omega
  · rintro z ⟨hz, hzero⟩
    have hs : sin z = 0 := (mul_eq_zero.mp hzero).resolve_left (by norm_num)
    obtain ⟨n, hn⟩ := Complex.sin_eq_zero_iff.mp hs
    have he : z = (Real.pi : ℂ)*n := hn.trans (mul_comm _ _)
    rw [he] at hz ⊢
    have hn := (free_center_mem_closedCentralCircle_iff N n).mp hz
    exact Finset.mem_image.mpr ⟨n, (by rw [Finset.mem_Icc]; omega), rfl⟩

end NLS.ZakharovShabat
