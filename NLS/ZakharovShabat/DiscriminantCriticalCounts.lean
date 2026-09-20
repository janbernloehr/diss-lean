import NLS.ZakharovShabat.FreeDerivativeZeroCounts

/-!
# Rouché counts for the intrinsic discriminant derivative

For each fixed even potential at finite p>1, all sufficiently distant free
discs contain one zero counted with analytic multiplicity, and every sufficiently
large central disc contains exactly 2N+1. The boundaries contain no zeros.
-/

noncomputable section
open Set Complex Metric
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The exterior derivative ratio gives the strict inequality needed for Rouché's theorem. -/
theorem exists_threshold_discriminant_derivative_rouche (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4) :
    ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → (∀ n : ℤ, r ≤ ‖z-(Real.pi : ℂ)*n‖) →
      ‖deriv (canonicalDiscriminant hp φ) z-(-2*sin z)‖ < ‖-2*sin z‖ := by
  obtain ⟨R, hR⟩ := exists_threshold_discriminant_derivative_div_free hp hp1 φ hφ hr hrπ
    (by norm_num : (0 : ℝ) < 1/2)
  refine ⟨R, ?_⟩
  intro z hz hsep
  have hs : -2*sin z ≠ 0 := mul_ne_zero (by norm_num)
    (sin_ne_zero_of_notMem_freeLattice (notMem_freeLattice_of_separated hr hsep))
  have h : ‖deriv (canonicalDiscriminant hp φ) z-(-2*sin z)‖/‖-2*sin z‖ ≤ (1 : ℝ)/2 := by
    rw [← norm_div, sub_div, div_self hs]
    exact hR z hz hsep
  exact (div_lt_one (norm_pos_iff.mpr hs)).mp (h.trans_lt (by norm_num))

/-- One cutoff supplies the strict boundary inequality on distant and central circles. -/
theorem exists_cutoff_discriminant_derivative_rouche (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4) :
    ∃ N : ℕ, 0 < N ∧
      (∀ n : ℤ, N ≤ n.natAbs → ∀ z ∈ sphere ((Real.pi : ℂ)*n) r,
        ‖deriv (canonicalDiscriminant hp φ) z-(-2*sin z)‖ < ‖-2*sin z‖) ∧
      (∀ K : ℕ, N ≤ K → ∀ z ∈ sphere 0 (centralCircleRadius K),
        ‖deriv (canonicalDiscriminant hp φ) z-(-2*sin z)‖ < ‖-2*sin z‖) := by
  obtain ⟨R, hR⟩ := exists_threshold_discriminant_derivative_rouche hp hp1 φ hφ hr hrπ
  obtain ⟨M, hM⟩ := exists_nat_gt ((R+r)/Real.pi)
  let N := M+1
  have hN : R+r ≤ Real.pi*(N : ℝ) := by
    have hM' : (R+r)/Real.pi ≤ (N : ℝ) := by dsimp [N]; push_cast; linarith
    exact (div_le_iff₀ Real.pi_pos).mp hM' |>.trans_eq (mul_comm _ _)
  refine ⟨N, by dsimp [N]; omega, ?_, ?_⟩
  · intro n hn z hz
    apply hR z _ (freeSphere_separated hr hrπ n hz)
    have hd : ‖z-(Real.pi : ℂ)*n‖ = r := by simpa only [mem_sphere, dist_eq_norm] using hz
    have hnorm : ‖(Real.pi : ℂ)*n‖ = Real.pi*(n.natAbs : ℝ) := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
        Complex.norm_intCast, Nat.cast_natAbs, Int.cast_abs]
    have ht := norm_sub_norm_le ((Real.pi : ℂ)*n) z
    rw [norm_sub_rev, hd, hnorm] at ht
    have hn' : (N : ℝ) ≤ (n.natAbs : ℝ) := by exact_mod_cast hn
    nlinarith [Real.pi_pos]
  · intro K hK z hz
    apply hR z _ (fun n => hrπ.trans ((by linarith [Real.pi_pos] : Real.pi/4 ≤ Real.pi/2).trans
      (centralCircle_lattice_gap K hz n)))
    have hz' : ‖z‖ = centralCircleRadius K := by simpa using hz
    have hK' : (N : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    rw [hz']
    unfold centralCircleRadius
    nlinarith [Real.pi_pos]

/-- The fixed-potential counting part of Lemma 8.3, including zero-free boundaries. -/
theorem exists_discriminant_critical_counts (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4) :
    ∃ N : ℕ, 0 < N ∧
      (∀ n : ℤ, N ≤ n.natAbs →
        analyticZeroCount (deriv (canonicalDiscriminant hp φ)) (closedBall ((Real.pi : ℂ)*n) r) = 1 ∧
        ∀ z ∈ sphere ((Real.pi : ℂ)*n) r, deriv (canonicalDiscriminant hp φ) z ≠ 0) ∧
      (∀ K : ℕ, N ≤ K →
        analyticZeroCount (deriv (canonicalDiscriminant hp φ)) (closedBall 0 (centralCircleRadius K)) = 2*K+1 ∧
        ∀ z ∈ sphere 0 (centralCircleRadius K), deriv (canonicalDiscriminant hp φ) z ≠ 0) := by
  obtain ⟨N, hN, hd, hc⟩ := exists_cutoff_discriminant_derivative_rouche hp hp1 φ hφ hr hrπ
  have ha := analyticOnNhd_discriminant_derivative hp hp1 φ hφ
  refine ⟨N, hN, ?_, ?_⟩
  · intro n hn
    refine ⟨?_, fun z hz => (rouche_ratio_mem_slitPlane (hd n hn z hz)).2.1⟩
    rw [analyticZeroCount_eq_of_boundary_lt hr (by intro z hz; fun_prop) (ha.mono (subset_univ _)) (hd n hn)]
    exact analyticZeroCount_free_derivative_disc hr.le (by linarith [Real.pi_pos]) n
  · intro K hK
    refine ⟨?_, fun z hz => (rouche_ratio_mem_slitPlane (hc K hK z hz)).2.1⟩
    rw [analyticZeroCount_eq_of_boundary_lt (centralCircleRadius_pos K)
      (by intro z hz; fun_prop) (ha.mono (subset_univ _)) (hc K hK)]
    exact analyticZeroCount_free_derivative_central K

end NLS.ZakharovShabat
