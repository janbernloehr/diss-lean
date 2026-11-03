import NLS.SequenceSpaces.AnalyticReciprocalTail
import NLS.ComplexAnalysis.CauchyFiniteHoles

/-! # An entire Hilbert basis at quadratically growing critical coordinates

Filled divided differences give entire scalar coordinates. Quadratic
critical growth gives a locally uniform reciprocal tail, hence a genuine
entire Hilbert-valued basis with the exact 2*pi*j normalization.
-/
noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis

def entireCriticalNumerator (g : ℂ → ℂ) (μ : ℕ+ → ℂ) (j : ℕ+) (z : ℂ) : ℂ :=
  (2*(j:ℂ)*Real.pi)*dslope g (μ j) z

def entireCriticalNumeratorCoordinates (g : ℂ → ℂ) (μ : ℕ+ → ℂ) (z : ℂ) (k : ℤ) : ℂ :=
  if hk : 0 < k then entireCriticalNumerator g μ (⟨k.toNat,by omega⟩ : ℕ+) z else 0

def entireCriticalNumeratorHilbert (g : ℂ → ℂ) (μ : ℕ+ → ℂ) (z : ℂ) : NLS.Coeff 2 :=
  NLS.Coeff.ofFunctionOrZero 2 (entireCriticalNumeratorCoordinates g μ z)

theorem entireCriticalNumerator_factor (g : ℂ → ℂ) (μ : ℕ+ → ℂ)
    (hz : ∀ j, g (μ j) = 0) (j : ℕ+) (z : ℂ) :
    (z-μ j)*entireCriticalNumerator g μ j z = (2*(j:ℂ)*Real.pi)*g z := by
  have h := sub_smul_dslope g (μ j) z
  simp only [smul_eq_mul,hz,sub_zero] at h
  unfold entireCriticalNumerator
  linear_combination (2*(j:ℂ)*Real.pi)*h

theorem entireCriticalNumerator_analytic (g : ℂ → ℂ) (μ : ℕ+ → ℂ)
    (hg : AnalyticOnNhd ℂ g univ) (j : ℕ+) :
    AnalyticOnNhd ℂ (entireCriticalNumerator g μ j) univ := by
  intro z _
  exact analyticAt_const.mul ((analyticOnNhd_dslope_of_analytic g univ (μ j) hg (mem_univ _)) z (mem_univ _))

theorem entireCriticalNumerator_local_tail (g : ℂ → ℂ) (μ : ℕ+ → ℂ)
    (hg : AnalyticOnNhd ℂ g univ) (hz : ∀ j, g (μ j) = 0)
    (c : ℝ) (hc : 0 < c) (N : ℕ)
    (hμ : ∀ j : ℕ+, N < (j:ℕ) → c*(j:ℝ)^2 ≤ ‖μ j‖) (z0 : ℂ) :
    ∃ U : Set ℂ, IsOpen U ∧ z0 ∈ U ∧
      ∃ M : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ U, ∀ j : ℕ+, M < (j:ℕ) →
        ‖entireCriticalNumerator g μ j z‖ ≤ K/(j:ℝ) := by
  let R := ‖z0‖+1
  let B := ‖g z0‖+1
  let U := ball z0 1 ∩ {z | ‖g z‖ < B}
  have hR : 0 < R := by dsimp only [R]; positivity
  have hB : 0 < B := by dsimp only [B]; positivity
  have hU : IsOpen U := isOpen_ball.inter (isOpen_lt hg.continuous.norm continuous_const)
  have hz0 : z0 ∈ U := ⟨mem_ball_self (by norm_num),by change ‖g z0‖ < B; dsimp only [B]; linarith⟩
  obtain ⟨M,hM⟩ := exists_nat_gt (2*R/c+1)
  refine ⟨U,hU,hz0,max N M,4*Real.pi*B/c,by positivity,?_⟩
  intro z hzU j hj
  have hjp : 0 < (j:ℝ) := by exact_mod_cast j.pos
  have hj1 : 1 ≤ (j:ℝ) := by exact_mod_cast j.pos
  have hMj : (M:ℝ) < (j:ℝ) := by exact_mod_cast (lt_of_le_of_lt (le_max_right N M) hj)
  have hNj : N < (j:ℕ) := (le_max_left _ _).trans_lt hj
  have hzR : ‖z‖ ≤ R := by
    have ht := norm_le_norm_sub_add z z0
    have hd : ‖z-z0‖ < 1 := by simpa only [mem_ball,dist_eq_norm] using hzU.1
    dsimp only [R]
    linarith
  have hRtail : R ≤ c/2*(j:ℝ)^2 := by
    have hm : 2*R/c < (j:ℝ) := by linarith
    have he := (div_lt_iff₀ hc).mp hm
    nlinarith [mul_nonneg hc.le (show 0 ≤ (j:ℝ)^2-(j:ℝ) by nlinarith)]
  have hden : c/2*(j:ℝ)^2 ≤ ‖z-μ j‖ := by
    have ht := norm_sub_norm_le (μ j) z
    rw [norm_sub_rev] at ht
    linarith [hμ j hNj]
  have hdenpos : 0 < c/2*(j:ℝ)^2 := by positivity
  have hne : z-μ j ≠ 0 := norm_pos_iff.mp (hdenpos.trans_le hden)
  have he : entireCriticalNumerator g μ j z = (2*(j:ℂ)*Real.pi)*g z/(z-μ j) :=
    (eq_div_iff hne).mpr ((mul_comm _ _).trans (entireCriticalNumerator_factor g μ hz j z))
  rw [he,norm_div,norm_mul,norm_mul,norm_mul]
  simp only [norm_ofNat,Complex.norm_natCast,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  calc
    _ ≤ (2*(j:ℝ)*Real.pi)*B/(c/2*(j:ℝ)^2) := by gcongr; exact hzU.2.le
    _ = _ := by field_simp; ring

theorem entireCriticalNumeratorHilbert_spec (g : ℂ → ℂ) (μ : ℕ+ → ℂ)
    (hg : AnalyticOnNhd ℂ g univ) (hz : ∀ j, g (μ j) = 0)
    (c : ℝ) (hc : 0 < c) (N : ℕ)
    (hμ : ∀ j : ℕ+, N < (j:ℕ) → c*(j:ℝ)^2 ≤ ‖μ j‖) :
    (∀ z k, entireCriticalNumeratorHilbert g μ z k = entireCriticalNumeratorCoordinates g μ z k) ∧
      AnalyticOnNhd ℂ (entireCriticalNumeratorHilbert g μ) univ := by
  have h := NLS.Coeff.analytic_l2_realization_of_local_reciprocal_tail
    (entireCriticalNumeratorCoordinates g μ) univ isOpen_univ ?_ ?_
  · exact ⟨fun z k => h.1 z (mem_univ _) k,h.2⟩
  · intro k
    by_cases hk : 0 < k
    · simpa only [entireCriticalNumeratorCoordinates,dif_pos hk] using
        entireCriticalNumerator_analytic g μ hg (⟨k.toNat,by omega⟩ : ℕ+)
    · simpa only [entireCriticalNumeratorCoordinates,dif_neg hk] using
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ => (0:ℂ)) univ)
  · intro z0 _
    obtain ⟨U,hU,hz0,M,K,hK,hb⟩ := entireCriticalNumerator_local_tail g μ hg hz c hc N hμ z0
    refine ⟨U,hU,hz0,subset_univ _,M,K,hK,?_⟩
    intro z hzU k hk
    by_cases hk0 : 0 < k
    · rw [entireCriticalNumeratorCoordinates,dif_pos hk0]
      have hj : M < k.toNat := by omega
      have he := hb z hzU (⟨k.toNat,by omega⟩ : ℕ+) hj
      change ‖entireCriticalNumerator g μ (⟨k.toNat,by omega⟩ : ℕ+) z‖ ≤ K/(k.toNat:ℝ) at he
      have hkcast : (k.toNat:ℝ) = (k:ℝ) := by rw [← Int.cast_natCast,Int.toNat_of_nonneg hk0.le]
      simpa only [hkcast,abs_of_pos (by exact_mod_cast hk0 : (0:ℝ) < k)] using! he
    · rw [entireCriticalNumeratorCoordinates,dif_neg hk0,norm_zero]
      positivity

end NLS.ComplexAnalysis
