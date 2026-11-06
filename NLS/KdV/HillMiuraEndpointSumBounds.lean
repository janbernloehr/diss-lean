import NLS.KdV.HillMiuraPositiveGaps
import NLS.KdV.HillMiuraRealEndpoints
import Mathlib.Topology.Order.Compact

/-! # Uniform positive-mode comparison for actual Miura endpoint sums

Canonical L2 endpoint displacements control the tail. Positivity of every
actual positive gap and a finite head bound include every low mode.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

private theorem positive_linear_comparison
    (f : ℕ → ℝ) (a D : ℝ) (ha : 0<a) (hD : 0≤D)
    (hf : ∀ n : ℕ, 0<f n)
    (hl : ∀ n : ℕ, a*((n : ℝ)+1)-D≤f n)
    (hu : ∀ n : ℕ, f n≤a*((n : ℝ)+1)+D) :
    ∃ A B : ℝ, 0<A ∧ 0<B ∧ ∀ n : ℕ,
      A*((n : ℝ)+2)≤f n ∧ f n≤B*((n : ℝ)+2) := by
  obtain ⟨N,hN⟩ := exists_nat_ge (2*D/a)
  let K : Set ℝ := range (fun i : Fin N => f i/((i : ℕ)+2 : ℝ))
  have hK : IsCompact K := (Set.finite_range _).isCompact
  obtain ⟨c,hc,hhead⟩ := hK.exists_forall_le' continuousOn_id (by
    intro x hx
    obtain ⟨i,rfl⟩ := hx
    exact div_pos (hf i) (by positivity))
  refine ⟨min (a/4) c,a+D+1,lt_min (by positivity) hc,by positivity,?_⟩
  intro n
  constructor
  · by_cases hn : N≤n
    · have hDN : 2*D≤a*(N : ℝ) := by
        have H := (div_le_iff₀ ha).mp hN
        nlinarith
      have hNn : (N : ℝ)≤n := by exact_mod_cast hn
      have htail : a/4*((n : ℝ)+2)≤f n := by
        have hmul := mul_le_mul_of_nonneg_left hNn ha.le
        nlinarith [hl n,show (0 : ℝ)≤n by positivity,
          mul_nonneg ha.le (show (0 : ℝ)≤n by positivity)]
      exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)).trans htail
    · have hnN : n<N := by omega
      have H : c≤f n/((n : ℝ)+2) := hhead _ ⟨⟨n,hnN⟩,rfl⟩
      exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)).trans
        ((le_div_iff₀ (by positivity : (0 : ℝ)<n+2)).mp H)
  · nlinarith [hu n,show (0 : ℝ)≤n by positivity,
      mul_nonneg hD (show (0 : ℝ)≤n by positivity)]

/-- Actual positive Dirac endpoint sums are comparable with the native
bracket at EVERY positive mode, with constants depending only on the lift. -/
theorem exists_hillMiura_positive_endpoint_sum_linear_bounds (u : PeriodOneRealL2) :
    ∃ A B : ℝ, 0<A ∧ 0<B ∧ ∀ n : ℕ,
      A*((n : ℝ)+2)≤(hillMiuraDiracLeft u.val (n+1)).re+(hillMiuraDiracRight u.val (n+1)).re ∧
      (hillMiuraDiracLeft u.val (n+1)).re+(hillMiuraDiracRight u.val (n+1)).re≤B*((n : ℝ)+2) := by
  let L : Coeff 2 := canonicalPeriodicLeftDisplacement (by simp) (by norm_num)
    (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _)
  let R : Coeff 2 := canonicalPeriodicRightDisplacement (by simp) (by norm_num)
    (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _)
  have hL (n : ℕ) : |(hillMiuraDiracLeft u.val (n+1)).re-Real.pi*((n : ℝ)+1)|≤‖L‖ := by
    have h := (abs_re_le_norm (L ((n+1 : ℕ) : ℤ))).trans
      (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞)≠0) L _)
    simpa [L,canonicalPeriodicLeftDisplacement_apply,hillMiuraDiracLeft] using h
  have hR (n : ℕ) : |(hillMiuraDiracRight u.val (n+1)).re-Real.pi*((n : ℝ)+1)|≤‖R‖ := by
    have h := (abs_re_le_norm (R ((n+1 : ℕ) : ℤ))).trans
      (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞)≠0) R _)
    simpa [R,canonicalPeriodicRightDisplacement_apply,hillMiuraDiracRight] using h
  apply positive_linear_comparison _ (2*Real.pi) (‖L‖+‖R‖) (by positivity) (by positivity)
  · intro n
    have hp := hillMiura_positive_gap_left_pos u ((n+1 : ℕ) : ℤ) (by positivity)
    have ho := hillMiuraDiracPair_ordered u.val ((n+1 : ℕ) : ℤ)
    change 0<(hillMiuraDiracLeft u.val (n+1)).re at hp
    exact add_pos hp (hp.trans_le ho)
  · intro n
    have hln := (abs_le.mp (hL n)).1
    have hrn := (abs_le.mp (hR n)).1
    linarith
  · intro n
    have hln := (abs_le.mp (hL n)).2
    have hrn := (abs_le.mp (hR n)).2
    linarith

end NLS.KdV
