import NLS.KdV.HillFreeSpectrum
import NLS.KdV.HillWideLocalization
import NLS.ComplexAnalysis.RealDiameterDisc

/-! # The central Hill characteristic count

An explicit circle encloses exactly the central real cluster and avoids
the actual characteristic zeros along the straight potential homotopy.
The free count is one simple root plus the preceding double lattice roots.
The resulting count fixes the offset needed for global spectral labels.
-/

noncomputable section
open Set Metric
open scoped Classical
namespace NLS.KdV

def hillCentralSeparator (N : ℕ) : ℝ := freeHillValue N-12*(N : ℝ)
def hillCentralCenter (N : ℕ) : ℂ := ((-(N : ℝ)^2+hillCentralSeparator N)/2 : ℝ)
def hillCentralRadius (N : ℕ) : ℝ := (hillCentralSeparator N-(-(N : ℝ)^2))/2
def hillCentralDisc (N : ℕ) : Set ℂ := closedBall (hillCentralCenter N) (hillCentralRadius N)

theorem freeHillValue_lt_centralSeparator (N : ℕ) (hN : 2 ≤ N) (k : ℕ) (hk : k < N) :
    freeHillValue k < hillCentralSeparator N := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hkR : (k : ℝ) ≤ N := by exact_mod_cast hk.le
  have hsq : (k : ℝ)^2 ≤ (N : ℝ)^2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr hkR
  have hgap := two_mul_nat_sub_one_le_abs_sq_sub_sq (n := N) (k := (k : ℤ))
    (by omega) (by simpa using ne_of_lt hk)
  simp only [Int.cast_natCast, abs_of_nonneg (sub_nonneg.mpr hsq)] at hgap
  have hd : 0 < (N : ℝ)^2-(k : ℝ)^2 := by linarith
  have hpi : 9 < Real.pi^2 := by nlinarith [Real.pi_gt_three]
  have hp := mul_pos (sub_pos.mpr hpi) hd
  unfold hillCentralSeparator freeHillValue
  push_cast
  nlinarith

theorem hillCentralSeparator_pos (N : ℕ) (hN : 2 ≤ N) : 0 < hillCentralSeparator N := by
  simpa [freeHillValue] using freeHillValue_lt_centralSeparator N hN 0 (by omega)

theorem hillCentralRadius_pos (N : ℕ) (hN : 2 ≤ N) : 0 < hillCentralRadius N := by
  unfold hillCentralRadius
  linarith [hillCentralSeparator_pos N hN, sq_nonneg (N : ℝ)]

theorem ofReal_mem_hillCentralDisc_iff (N : ℕ) (x : ℝ) :
    (x : ℂ) ∈ hillCentralDisc N ↔ x ∈ Icc (-(N : ℝ)^2) (hillCentralSeparator N) :=
  ComplexAnalysis.ofReal_mem_realDiameter_closedBall_iff _ _ _

theorem freeHillValue_mem_hillCentralDisc_iff (N : ℕ) (hN : 2 ≤ N) (k : ℕ) :
    (freeHillValue k : ℂ) ∈ hillCentralDisc N ↔ k < N := by
  rw [ofReal_mem_hillCentralDisc_iff]
  constructor
  · intro h
    by_contra! hk
    have hmon := strictMono_freeHillValue.monotone hk
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    unfold hillCentralSeparator at h
    linarith [h.2]
  · intro hk
    exact ⟨(neg_nonpos.mpr (sq_nonneg (N : ℝ))).trans (by unfold freeHillValue; positivity),
      (freeHillValue_lt_centralSeparator N hN k hk).le⟩

/-- Exact free central count: one simple lowest root and N-1 double roots. -/
theorem hillL2Radicand_free_central_count (N : ℕ) (hN : 2 ≤ N) :
    ComplexAnalysis.analyticZeroCount (hillL2Radicand 0) (hillCentralDisc N) = 2*N-1 := by
  let S := (Finset.range N).image (fun k : ℕ => (freeHillValue k : ℂ))
  have hs : (S : Set ℂ) ⊆ hillCentralDisc N := by
    intro z hz
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hz
    exact (freeHillValue_mem_hillCentralDisc_iff N hN k).mpr (Finset.mem_range.mp hk)
  have hcover : hillCentralDisc N ∩ (hillL2Radicand 0) ⁻¹' {0} ⊆ S := by
    rintro z ⟨hz,hz0⟩
    obtain ⟨k,rfl⟩ := (hillL2Radicand_free_zero_iff z).mp hz0
    exact Finset.mem_image.mpr ⟨k,Finset.mem_range.mpr
      ((freeHillValue_mem_hillCentralDisc_iff N hN k).mp hz),rfl⟩
  rw [ComplexAnalysis.analyticZeroCount_eq_sum S hs hcover]
  dsimp only [S]
  rw [Finset.sum_image]
  · have ho (k : ℕ) : analyticOrderNatAt (hillL2Radicand 0) (freeHillValue k : ℂ) =
        if k = 0 then 1 else 2 := by
      by_cases hk : k = 0
      · subst k
        simpa [freeHillValue] using hillL2Radicand_free_order_zero
      · rw [if_neg hk]
        exact hillL2Radicand_free_order k (by omega)
    simp_rw [ho]
    obtain ⟨M,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
    rw [Finset.sum_range_succ']
    simp
    omega
  · intro a _ b _ he
    exact strictMono_freeHillValue.injective (Complex.ofReal_injective he)

/-- The actual central contour is zero-free on the entire real L2 ball
at the stated cutoff. Reality excludes the nonreal part of the circle. -/
theorem hillL2Radicand_ne_zero_on_central_sphere
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (N : ℕ) (hN : 2 ≤ N) (hcut : 8*‖q‖ ≤ (N : ℝ))
    (z : ℂ) (hz : z ∈ sphere (hillCentralCenter N) (hillCentralRadius N)) :
    hillL2Radicand (SpectralWeight.one.toCoeff q) z ≠ 0 := by
  apply ComplexAnalysis.ne_zero_on_realDiameter_sphere
    (hillL2Radicand (SpectralWeight.one.toCoeff q)) (-(N : ℝ)^2) (hillCentralSeparator N)
    (by linarith [hillCentralSeparator_pos N hN, sq_nonneg (N : ℝ)])
    (fun w hw => hillL2Discriminant_root_im_zero q hq hreal w (sub_eq_zero.mp hw))
    ?_ ?_ z hz
  · intro hd
    have h := hillL2Radicand_re_lower_bound q hq N (by omega) hcut _ hd
    exact (lt_irrefl _ h)
  · exact hillL2Radicand_ne_zero_on_central_separator q hq N hN hcut _ rfl

/-- The exact actual central count on the full real, period-one L2 domain. -/
theorem hillL2Radicand_central_count
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (N : ℕ) (hN : 2 ≤ N) (hcut : 8*‖q‖ ≤ (N : ℝ)) :
    ComplexAnalysis.analyticZeroCount (hillL2Radicand (SpectralWeight.one.toCoeff q))
      (hillCentralDisc N) = 2*N-1 := by
  let F : Icc (0 : ℝ) 1 → ℂ → ℂ := fun t z =>
    hillL2Radicand ((t.val : ℂ) • SpectralWeight.one.toCoeff q) z
  have hcont : Continuous F.uncurry := by
    dsimp only [F, Function.uncurry]
    have hc : Continuous (fun p : ℂ × Coeff 2 => hillL2Radicand p.2 p.1) :=
      continuous_iff_continuousAt.mpr
        (fun p => (analyticOnNhd_hillL2Radicand_joint p (mem_univ _)).continuousAt)
    have hm : Continuous (fun p : Icc (0 : ℝ) 1 × ℂ =>
        (p.2, (p.1.val : ℂ) • SpectralWeight.one.toCoeff q)) := by
      have ht : Continuous (fun p : Icc (0 : ℝ) 1 × ℂ => (p.1.val : ℂ)) :=
        Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)
      have hq' : Continuous (fun _ : Icc (0 : ℝ) 1 × ℂ => SpectralWeight.one.toCoeff q) :=
        continuous_const
      exact continuous_snd.prodMk (ht.smul hq')
    convert! hc.comp hm using 1
  have hnorm (t : Icc (0 : ℝ) 1) : ‖(t.val : ℂ) • q‖ ≤ ‖q‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg t.property.1]
    exact mul_le_of_le_one_left (norm_nonneg q) t.property.2
  have hz (t : Icc (0 : ℝ) 1) (z : ℂ)
      (hzc : z ∈ sphere (hillCentralCenter N) (hillCentralRadius N)) : F t z ≠ 0 := by
    have hpar : SpectralWeight.one.toCoeff ((t.val : ℂ) • q) ∈ Coeff.paritySubspace 0 := by
      rw [map_smul]
      exact (Coeff.paritySubspace 0).smul_mem _ hq
    have hreal' : IsRealHillPotential (SpectralWeight.one.toCoeff ((t.val : ℂ) • q)) := by
      rw [map_smul]
      exact hreal.smul_real t.val
    have hcut' : 8*‖(t.val : ℂ) • q‖ ≤ (N : ℝ) := by linarith [hnorm t]
    simpa only [F, map_smul] using
      hillL2Radicand_ne_zero_on_central_sphere _ hpar hreal' N hN hcut' z hzc
  have he := ComplexAnalysis.analyticZeroCount_eq_of_homotopy F
    (hillCentralCenter N) (hillCentralRadius N) (hillCentralRadius_pos N hN) hcont.continuousOn
    (fun _ => (analyticOnNhd_hillL2Radicand _).mono (subset_univ _)) hz
    (⟨1,by norm_num⟩ : Icc (0 : ℝ) 1) (⟨0,by norm_num⟩ : Icc (0 : ℝ) 1)
  have he' : ComplexAnalysis.analyticZeroCount (hillL2Radicand (SpectralWeight.one.toCoeff q))
      (hillCentralDisc N) = ComplexAnalysis.analyticZeroCount (hillL2Radicand 0) (hillCentralDisc N) := by
    simpa only [hillCentralDisc, F, Complex.ofReal_one, one_smul, Complex.ofReal_zero, zero_smul] using he
  exact he'.trans (hillL2Radicand_free_central_count N hN)

/-- The circle count is exactly the count of the actual real central interval. -/
theorem hillL2Radicand_central_interval_count
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (N : ℕ) (hN : 2 ≤ N) (hcut : 8*‖q‖ ≤ (N : ℝ)) :
    ComplexAnalysis.analyticZeroCount (hillL2Radicand (SpectralWeight.one.toCoeff q))
      {z : ℂ | z.im = 0 ∧ z.re ∈ Ioo (-(N : ℝ)^2) (hillCentralSeparator N)} = 2*N-1 := by
  rw [← hillL2Radicand_central_count q hq hreal N hN hcut]
  apply ComplexAnalysis.analyticZeroCount_congr_set
  intro z hd
  have him := hillL2Discriminant_root_im_zero q hq hreal z (sub_eq_zero.mp hd)
  have he : (z.re : ℂ) = z := by apply Complex.ext <;> simp [him]
  have hlo := hillL2Radicand_re_lower_bound q hq N (by omega) hcut z hd
  have hne : z.re ≠ hillCentralSeparator N := by
    intro hz
    exact hillL2Radicand_ne_zero_on_central_separator q hq N hN hcut z hz hd
  rw [← he, ofReal_mem_hillCentralDisc_iff]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mem_ofPred_eq, true_and, mem_Ioo, mem_Icc]
  exact ⟨fun h => ⟨h.1.le,h.2.le⟩,fun h => ⟨hlo,lt_of_le_of_ne h.2 hne⟩⟩

end NLS.KdV
