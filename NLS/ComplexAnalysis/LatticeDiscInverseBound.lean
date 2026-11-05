import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic

/-! # Uniform reciprocal bounds on zero-excluding lattice discs

Bounded radii and bounded displacement of disc centers from the physical
lattice give one reciprocal bound of order 1/(1+|n|), at every noncentral
index and every point in the closed disc. Finitely many central discs
are handled without any gap-length or action division.
-/
noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis

theorem exists_latticeDisc_inverse_bound (c : ℤ → ℂ) (r : ℤ → ℝ) (M B : ℝ)
    (hc : ∀ n, ‖c n-(Real.pi : ℂ)*n‖ ≤ M) (hr : ∀ n, r n ≤ B)
    (hzero : ∀ n : ℤ, n ≠ 0 → (0 : ℂ) ∉ closedBall (c n) (r n)) :
    ∃ D : ℝ, 0 < D ∧ ∀ n : ℤ, n ≠ 0 → ∀ z ∈ closedBall (c n) (r n),
      ‖z⁻¹‖ ≤ D/(1+|(n : ℝ)|) := by
  classical
  let δ : ℤ → ℝ := fun n => ‖c n‖-r n
  have hδ (n : ℤ) (hn : n ≠ 0) : 0 < δ n := by
    have hlt : r n < ‖c n‖ := by
      by_contra h
      apply hzero n hn
      simpa only [mem_closedBall,dist_zero_left] using le_of_not_gt h
    exact sub_pos.mpr hlt
  obtain ⟨N,hN⟩ := exists_nat_ge (max (1 : ℝ) (2*(M+B)/Real.pi))
  let S : Finset ℤ := (Finset.Icc (-(N : ℤ)) N).erase 0
  let f : ℤ → ℝ := fun n => (1+|(n : ℝ)|)/δ n
  obtain ⟨K,hK⟩ := (S.finite_toSet.image f).bddAbove
  let D := max K (max (4/Real.pi) 1)
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one ((le_max_right (4/Real.pi) 1).trans (le_max_right K _))
  refine ⟨D,hD,?_⟩
  intro n hn z hz
  have hq : 0 < 1+|(n : ℝ)| := by positivity
  have hweight : 1+|(n : ℝ)| ≤ D*δ n := by
    by_cases hs : n ∈ S
    · have hk : f n ≤ K := hK ⟨n,hs,rfl⟩
      have he := (div_le_iff₀ (hδ n hn)).mp hk
      exact he.trans (mul_le_mul_of_nonneg_right (le_max_left K _) (hδ n hn).le)
    · have hnot : n ∉ Finset.Icc (-(N : ℤ)) N := by
        intro h
        exact hs (Finset.mem_erase.mpr ⟨hn,h⟩)
      have habs : (N : ℤ) < |n| := by
        simp only [Finset.mem_Icc] at hnot
        by_contra h
        exact hnot (abs_le.mp (le_of_not_gt h))
      have habsR : (N : ℝ) < |(n : ℝ)| := by exact_mod_cast habs
      have hn1 : 1 ≤ |(n : ℝ)| := (le_max_left 1 _).trans (hN.trans habsR.le)
      have hh : 2*(M+B) ≤ |(n : ℝ)| * Real.pi :=
        (div_le_iff₀ Real.pi_pos).mp ((le_max_right 1 _).trans (hN.trans habsR.le))
      have hlat : Real.pi * |(n : ℝ)| ≤ ‖c n‖+M := by
        have h := norm_le_norm_sub_add ((Real.pi : ℂ)*n) (c n)
        have hd : ‖(Real.pi : ℂ)*n-c n‖ ≤ M := by rw [norm_sub_rev]; exact hc n
        simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,
          Complex.norm_intCast] at h
        linarith
      have hfour : (1+|(n : ℝ)|)*Real.pi ≤ 4*δ n := by
        dsimp only [δ]
        nlinarith [hr n,Real.pi_pos]
      have he : 1+|(n : ℝ)| ≤ (4/Real.pi)*δ n := by
        calc
          _ ≤ (4*δ n)/Real.pi := (le_div_iff₀ Real.pi_pos).mpr hfour
          _ = _ := by ring
      exact he.trans (mul_le_mul_of_nonneg_right
        ((le_max_left (4/Real.pi) 1).trans (le_max_right K _)) (hδ n hn).le)
  have hnorm : δ n ≤ ‖z‖ := by
    have h := norm_le_norm_sub_add (c n) z
    have hd : ‖c n-z‖ ≤ r n := by
      rw [norm_sub_rev]
      simpa only [dist_eq_norm] using mem_closedBall.mp hz
    dsimp only [δ]
    linarith
  have hzpos : 0 < ‖z‖ := (hδ n hn).trans_le hnorm
  apply (le_div_iff₀ hq).mpr
  rw [norm_inv]
  calc
    ‖z‖⁻¹*(1+|(n : ℝ)|) = (1+|(n : ℝ)|)/‖z‖ := by ring
    _ ≤ D := (div_le_iff₀ hzpos).mpr
      (hweight.trans (mul_le_mul_of_nonneg_left hnorm hD.le))

end NLS.ComplexAnalysis
