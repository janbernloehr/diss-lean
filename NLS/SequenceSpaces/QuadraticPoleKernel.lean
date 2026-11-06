import NLS.SequenceSpaces.AnalyticReciprocalTail

/-! # Genuine Hilbert kernels for quadratically growing poles

The complement of the selected poles is open by a finite-head and uniform-tail
argument. The squared reciprocal kernel is realized in l2 on this domain;
no completeness assertion about any other spectral zero set is required.
-/
noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.Coeff

def positivePoleIndex (k : ℤ) (hk : 0 < k) : ℕ+ := ⟨k.toNat,by omega⟩

theorem positivePoleIndex_real (k : ℤ) (hk : 0 < k) :
    (positivePoleIndex k hk : ℝ) = k := by
  simp only [positivePoleIndex,PNat.mk_coe]
  exact_mod_cast Int.toNat_of_nonneg (le_of_lt hk)

def quadraticPoleDomain (mu : ℕ+ → ℂ) : Set ℂ :=
  {z | ∀ n, z-mu n ≠ 0}

def quadraticPoleCoordinates (mu : ℕ+ → ℂ) (z : ℂ) (k : ℤ) : ℂ :=
  if hk : 0 < k then (k : ℂ)/(z-mu (positivePoleIndex k hk))^2 else 0

def quadraticPoleKernel (mu : ℕ+ → ℂ) (z : ℂ) : Coeff 2 :=
  ofFunctionOrZero 2 (quadraticPoleCoordinates mu z)

theorem exists_quadratic_pole_tail (mu : ℕ+ → ℂ) (a : ℝ) (ha : 0 < a)
    (hg : ∀ n : ℕ+, a*(n : ℝ)^2 ≤ ‖mu n‖) (x : ℂ) :
    ∃ M : ℕ, ∀ z ∈ ball x 1, ∀ n : ℕ+, M < (n : ℕ) →
      a/2*(n : ℝ)^2 ≤ ‖z-mu n‖ := by
  let R := ‖x‖+1
  obtain ⟨M,hM⟩ := exists_nat_gt (2*R/a+1)
  refine ⟨M,?_⟩
  intro z hz n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.property
  have hmn : (M : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have he := (div_lt_iff₀ ha).mp (show 2*R/a < (n : ℝ) by linarith)
  have hR : R ≤ a/2*(n : ℝ)^2 := by
    nlinarith [mul_nonneg ha.le (show (0 : ℝ) ≤ (n : ℝ)^2-(n : ℝ) by nlinarith)]
  have hzR : ‖z‖ ≤ R := by
    have hd : ‖z-x‖ < 1 := by simpa only [mem_ball,dist_eq_norm] using hz
    have ht := norm_le_norm_sub_add z x
    dsimp only [R]
    linarith
  have ht := norm_sub_norm_le (mu n) z
  rw [norm_sub_rev] at ht
  have hgn := hg n
  linarith

theorem isOpen_quadraticPoleDomain (mu : ℕ+ → ℂ) (a : ℝ) (ha : 0 < a)
    (hg : ∀ n : ℕ+, a*(n : ℝ)^2 ≤ ‖mu n‖) : IsOpen (quadraticPoleDomain mu) := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨M,hM⟩ := exists_quadratic_pole_tail mu a ha hg x
  let U : Set ℂ := ball x 1 ∩ ⋂ n ∈ Finset.range M, {z | z-mu ⟨n+1,by omega⟩ ≠ 0}
  have hU : IsOpen U := by
    apply isOpen_ball.inter
    apply isOpen_biInter_finset
    intro n hn
    exact isOpen_ne_fun (continuous_id.sub continuous_const) continuous_const
  have hxU : x ∈ U := by
    refine ⟨mem_ball_self (by norm_num),?_⟩
    simp only [mem_iInter,mem_ofPred_eq]
    intro n _
    exact hx ⟨n+1,by omega⟩
  apply mem_of_superset (hU.mem_nhds hxU)
  intro z hz n
  by_cases hn : (n : ℕ) ≤ M
  · have hnpos : 0 < (n : ℕ) := n.property
    have hidx : (n : ℕ)-1 < M := by omega
    have he := mem_iInter₂.mp hz.2 ((n : ℕ)-1) (Finset.mem_range.mpr hidx)
    have heq : (⟨(n : ℕ)-1+1,by omega⟩ : ℕ+) = n := by
      apply Subtype.ext
      change (n : ℕ)-1+1 = (n : ℕ)
      omega
    change z-mu ⟨(n : ℕ)-1+1,by omega⟩ ≠ 0 at he
    rw [heq] at he
    exact he
  · exact norm_pos_iff.mp ((by positivity : 0 < a/2*(n : ℝ)^2).trans_le
      (hM z hz.1 n (by omega)))

theorem quadraticPoleKernel_spec (mu : ℕ+ → ℂ) (a : ℝ) (ha : 0 < a)
    (hg : ∀ n : ℕ+, a*(n : ℝ)^2 ≤ ‖mu n‖) :
    (∀ z ∈ quadraticPoleDomain mu, ∀ k,
      quadraticPoleKernel mu z k = quadraticPoleCoordinates mu z k) ∧
      AnalyticOnNhd ℂ (quadraticPoleKernel mu) (quadraticPoleDomain mu) := by
  have hD := isOpen_quadraticPoleDomain mu a ha hg
  apply analytic_l2_realization_of_local_reciprocal_tail _ _ hD
  · intro k z hz
    by_cases hk : 0 < k
    · simpa only [quadraticPoleCoordinates,dif_pos hk] using!
        (analyticAt_const.div ((analyticAt_id.sub analyticAt_const).pow 2)
          (pow_ne_zero 2 (hz (positivePoleIndex k hk))))
    · simpa only [quadraticPoleCoordinates,dif_neg hk] using
        (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) z)
  intro x hx
  obtain ⟨M,hM⟩ := exists_quadratic_pole_tail mu a ha hg x
  refine ⟨ball x 1 ∩ quadraticPoleDomain mu,isOpen_ball.inter hD,
    ⟨mem_ball_self (by norm_num),hx⟩,fun _ hz => hz.2,M,4/a^2,by positivity,?_⟩
  intro z hz k hkM
  by_cases hk : 0 < k
  · let n := positivePoleIndex k hk
    have hnM : M < (n : ℕ) := by change M < k.toNat; omega
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.property
    have hb := hM z hz.1 n hnM
    have hd : 0 < a/2*(n : ℝ)^2 := by positivity
    rw [quadraticPoleCoordinates,dif_pos hk]
    change ‖(k : ℂ)/(z-mu n)^2‖ ≤ _
    rw [norm_div,norm_pow,Complex.norm_intCast,abs_of_pos (by exact_mod_cast hk : (0 : ℝ) < k)]
    have hnr : (n : ℝ) = k := positivePoleIndex_real k hk
    rw [← hnr]
    have hb' : a/2*(n : ℝ) ≤ ‖z-mu n‖ := by
      have ht : a/2*(n : ℝ) ≤ a/2*(n : ℝ)^2 := by nlinarith
      exact ht.trans hb
    calc
      _ ≤ (n : ℝ)/(a/2*(n : ℝ))^2 := by gcongr
      _ = (4/a^2)/(n : ℝ) := by field_simp; ring
  · simp only [quadraticPoleCoordinates,dif_neg hk,norm_zero]
    positivity

theorem quadraticPoleKernel_positive (mu : ℕ+ → ℂ) (a : ℝ) (ha : 0 < a)
    (hg : ∀ n : ℕ+, a*(n : ℝ)^2 ≤ ‖mu n‖) (z : ℂ) (hz : z ∈ quadraticPoleDomain mu)
    (n : ℕ+) : quadraticPoleKernel mu z (n : ℤ) = (n : ℂ)/(z-mu n)^2 := by
  rw [(quadraticPoleKernel_spec mu a ha hg).1 z hz,quadraticPoleCoordinates,
    dif_pos (by exact_mod_cast n.pos)]
  congr 2

end NLS.Coeff
