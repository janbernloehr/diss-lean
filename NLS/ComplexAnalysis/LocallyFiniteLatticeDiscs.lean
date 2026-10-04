import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.LocallyFinite

/-! # Local finiteness of discs with lattice tails

Only finitely many disc centers and radii may differ from a fixed
positive-spacing lattice with uniformly bounded radii.
-/
noncomputable section
open Set Metric Filter Topology Complex
namespace NLS.ComplexAnalysis

theorem locallyFinite_closedBall_of_lattice_tail (c : ℤ → ℂ) (R : ℤ → ℝ)
    (N : ℕ) (a b : ℝ) (ha : 0 < a)
    (htail : ∀ n : ℤ, N < n.natAbs → c n = (a:ℂ)*n ∧ R n ≤ b) :
    LocallyFinite (fun n => closedBall (c n) (R n)) := by
  intro z
  obtain ⟨K,hK⟩ := exists_nat_gt ((‖z‖+1+b)/a)
  let M := max N K
  refine ⟨ball z 1,ball_mem_nhds z (by norm_num),?_⟩
  apply (Set.finite_Icc (-(M:ℤ)) (M:ℤ)).subset
  intro n hn
  obtain ⟨w,hw,hwz⟩ := hn
  have hnM : n.natAbs ≤ M := by
    by_contra hnM
    have hnN : N < n.natAbs := lt_of_le_of_lt (le_max_left _ _) (lt_of_not_ge hnM)
    have hnK : K < n.natAbs := lt_of_le_of_lt (le_max_right _ _) (lt_of_not_ge hnM)
    obtain ⟨hc,hR⟩ := htail n hnN
    have hwc : ‖w-c n‖ ≤ b := by simpa only [dist_eq_norm] using (mem_closedBall.mp hw).trans hR
    have hwz' : ‖w-z‖ < 1 := by simpa only [dist_eq_norm] using mem_ball.mp hwz
    have hwbound : ‖w‖ < ‖z‖+1 := by
      have h := norm_add_le (w-z) z
      rw [sub_add_cancel] at h
      linarith
    have hcBound : ‖c n‖ < ‖z‖+1+b := by
      have h := norm_sub_le w (w-c n)
      have he : w-(w-c n) = c n := by ring
      rw [he] at h
      linarith
    have hnorm : ‖c n‖ = a*(n.natAbs:ℝ) := by
      rw [hc,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha,Complex.norm_intCast]
      congr 1
      simpa only [Int.cast_abs] using (Nat.cast_natAbs (α := ℝ) n).symm
    rw [hnorm] at hcBound
    have hKn : (K:ℝ) < (n.natAbs:ℝ) := by exact_mod_cast hnK
    have hbK : ‖z‖+1+b < (K:ℝ)*a := (div_lt_iff₀ ha).mp hK
    nlinarith
  change -(M:ℤ) ≤ n ∧ n ≤ (M:ℤ)
  omega

/-- A compact nonempty set strictly inside a ball fits in a smaller
concentric ball with a positive radius. -/
theorem exists_inner_radius_of_isCompact_subset_ball (K : Set ℂ) (c : ℂ) (R : ℝ)
    (hK : IsCompact K) (hne : K.Nonempty) (hsub : K ⊆ ball c R) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ K ⊆ ball c r := by
  obtain ⟨z,hz,hmax⟩ := hK.exists_isMaxOn hne (continuous_id.dist continuous_const).continuousOn
  change ∀ w ∈ K, dist w c ≤ dist z c at hmax
  have hzR := mem_ball.mp (hsub hz)
  refine ⟨(dist z c+R)/2,?_,by linarith,?_⟩
  · have := dist_nonneg (x := z) (y := c)
    linarith
  · intro w hw
    exact mem_ball.mpr (lt_of_le_of_lt (hmax w hw) (by linarith))

end NLS.ComplexAnalysis
