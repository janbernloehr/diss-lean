import NLS.KdV.HillHminusOneReality
import NLS.KdV.HillHminusOneCentralCounting

/-! # Ordered real H^-1 high pairs and their global order

The actual pair retains analytic multiplicities. The free-energy spacing
orders distinct high pairs and separates them from the central cluster.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.KdV

structure HillHminusRealHighPair (q : PeriodOneHminusOne) (n : ℕ+) (r : ℝ) where
  left : ℝ
  right : ℝ
  ordered : left ≤ right
  pair : HillHminusHighGapPair q n r (left : ℂ) (right : ℂ)

theorem exists_hillHminus_real_high_pairs (q : PeriodOneHminusOne) :
    ∃ r : ℝ, 0 < r ∧ r ≤ Real.pi/4 ∧ ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne,
      0 < N ∧ IsOpen V ∧ q ∈ V ∧ ∀ n : ℕ+, N ≤ (n : ℕ) →
        ∀ a ∈ V, IsRealPeriodOneHminusOne a → Nonempty (HillHminusRealHighPair a n r) := by
  obtain ⟨r,N,V,hr,hrpi,hN,hV,hq,hfamily⟩ := exists_hillHminus_high_gap_pairs q
  refine ⟨r,hr,hrpi,N,V,hN,hV,hq,?_⟩
  intro n hn a ha hreal
  obtain ⟨_,_,_,_,_,_,hpairs⟩ := hfamily n hn
  obtain ⟨_,l,u,hpair,_⟩ := hpairs a ha
  have hl : l = (l.re : ℂ) := by
    apply Complex.ext <;> simp [hillHminusRadicand_root_im_zero a hreal l hpair.left_zero]
  have hu : u = (u.re : ℂ) := by
    apply Complex.ext <;> simp [hillHminusRadicand_root_im_zero a hreal u hpair.right_zero]
  rw [hl,hu] at hpair
  by_cases hle : l.re ≤ u.re
  · exact ⟨⟨l.re,u.re,hle,hpair⟩⟩
  · exact ⟨⟨u.re,l.re,(le_of_not_ge hle),hpair.swap⟩⟩

theorem HillHminusRealHighPair.localization
    {q : PeriodOneHminusOne} {n : ℕ+} {r : ℝ}
    (p : HillHminusRealHighPair q n r) (hr : r ≤ Real.pi/4) :
    |p.left-freeHillValue (n : ℕ)| ≤ 4*(n : ℝ) ∧
      |p.right-freeHillValue (n : ℕ)| ≤ 4*(n : ℝ) := by
  have hcenter : ((Real.pi : ℂ)*(n : ℕ))^2 = (freeHillValue (n : ℕ) : ℂ) := by
    dsimp only [freeHillValue]; push_cast; ring
  have hrad : Real.pi*(n : ℕ)*r ≤ 4*(n : ℝ) := by
    have hpi : Real.pi^2 < 16 := by nlinarith [Real.pi_lt_four,Real.pi_pos]
    have hnpos : (0 : ℝ) < (n : ℕ) := by positivity
    have hh := mul_le_mul_of_nonneg_left hr Real.pi_pos.le
    nlinarith
  constructor
  · have hh := p.pair.left_mem
    rw [hcenter,mem_ball,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs] at hh
    exact hh.le.trans hrad
  · have hh := p.pair.right_mem
    rw [hcenter,mem_ball,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs] at hh
    exact hh.le.trans hrad

theorem centralSeparator_lt_freeHillValue_sub_four
    (N n : ℕ) (hN : 2 ≤ N) (hn : N ≤ n) :
    hillCentralSeparator N < freeHillValue n-4*(n : ℝ) := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hs : (n : ℝ)-(N : ℝ) ≤ (n : ℝ)^2-(N : ℝ)^2 := by
    nlinarith [mul_nonneg (show 0 ≤ (n : ℝ)-(N : ℝ) by linarith)
      (show 0 ≤ (n : ℝ)+(N : ℝ)-1 by linarith)]
  have hpi : 4 ≤ Real.pi^2 := by nlinarith [Real.pi_gt_three]
  have hp := mul_nonneg (sub_nonneg.mpr hpi) (show 0 ≤ (n : ℝ)^2-(N : ℝ)^2 by linarith)
  unfold hillCentralSeparator freeHillValue
  push_cast
  nlinarith

theorem HillHminusRealHighPair.above_central_separator
    {q : PeriodOneHminusOne} {n : ℕ+} {r : ℝ}
    (p : HillHminusRealHighPair q n r) (hr : r ≤ Real.pi/4)
    (N : ℕ) (hN : 2 ≤ N) (hn : N ≤ (n : ℕ)) : hillCentralSeparator N < p.left := by
  have hloc := (p.localization hr).1
  have hs := centralSeparator_lt_freeHillValue_sub_four N (n : ℕ) hN hn
  linarith [(abs_le.mp hloc).1]

theorem HillHminusRealHighPair.separated
    {q : PeriodOneHminusOne} {n m : ℕ+} {r : ℝ}
    (p : HillHminusRealHighPair q n r) (s : HillHminusRealHighPair q m r)
    (hr : r ≤ Real.pi/4) (hnm : (n : ℕ) < (m : ℕ)) : p.right < s.left := by
  have hp := (p.localization hr).2
  have hs := (s.localization hr).1
  have hnmR : (n : ℝ)+1 ≤ (m : ℝ) := by exact_mod_cast hnm
  have hnpos : (0 : ℝ) < n := by positivity
  have hsq : (n : ℝ)+(m : ℝ) ≤ (m : ℝ)^2-(n : ℝ)^2 := by
    nlinarith [mul_nonneg (show 0 ≤ (m : ℝ)-(n : ℝ)-1 by linarith)
      (show 0 ≤ (m : ℝ)+(n : ℝ) by positivity)]
  have hpi : 9 < Real.pi^2 := by nlinarith [Real.pi_gt_three]
  have hprod := mul_pos (sub_pos.mpr hpi) (show 0 < (m : ℝ)^2-(n : ℝ)^2 by linarith)
  dsimp only [freeHillValue] at hp hs
  push_cast at hp hs
  nlinarith [(abs_le.mp hp).2,(abs_le.mp hs).1]

end NLS.KdV
