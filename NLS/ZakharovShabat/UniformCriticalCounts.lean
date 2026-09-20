import NLS.ZakharovShabat.FreeExteriorCutoffs
import NLS.ZakharovShabat.LocallyUniformDiscriminantAsymptotics
import NLS.ZakharovShabat.DiscriminantCriticalDistribution

/-!
# Critical-point counts on one potential neighborhood

The derivative ratio bound with tolerance one half supplies a common spectral
threshold. Pure free-circle geometry converts it to one integer cutoff for
Rouché counts, boundary nonvanishing, and exhaustion at every nearby even
potential. The real-type assertion is treated separately.
-/

noncomputable section
open Set Complex Metric
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The strict Rouché inequality holds on a common exterior for every nearby even potential. -/
theorem exists_uniform_discriminant_derivative_rouche (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4) :
    ∃ U : Set (PairSpace p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∃ R : ℝ, ∀ ψ ∈ U, ψ ∈ pairParitySubspace 0 → ∀ z : ℂ, R ≤ ‖z‖ →
        (∀ n : ℤ, r ≤ ‖z-(Real.pi : ℂ)*n‖) →
        ‖deriv (canonicalDiscriminant hp ψ) z-(-2*sin z)‖ < ‖-2*sin z‖ := by
  obtain ⟨U, ho, hconv, hφ, h0, R, hb⟩ := exists_uniform_discriminant_derivative_div_free hp hp1 φ hr hrπ
    (by norm_num : (0 : ℝ) < 1/2)
  refine ⟨U, ho, hconv, hφ, h0, R, ?_⟩
  intro ψ hψ heven z hz hsep
  have hs : -2*sin z ≠ 0 := mul_ne_zero (by norm_num)
    (sin_ne_zero_of_notMem_freeLattice (notMem_freeLattice_of_separated hr hsep))
  have h : ‖deriv (canonicalDiscriminant hp ψ) z-(-2*sin z)‖/‖-2*sin z‖ ≤ (1 : ℝ)/2 := by
    rw [← norm_div, sub_div, div_self hs]
    exact hb ψ hψ heven z hz hsep
  exact (div_lt_one (norm_pos_iff.mpr hs)).mp (h.trans_lt (by norm_num))

/-- One neighborhood and integer cutoff give all distant and central counts and exhaust the critical points. -/
theorem exists_uniform_discriminant_critical_counts (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4) :
    ∃ N : ℕ, 0 < N ∧ ∃ U : Set (PairSpace p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U, ψ ∈ pairParitySubspace 0 →
        (∀ n : ℤ, N ≤ n.natAbs →
          analyticZeroCount (deriv (canonicalDiscriminant hp ψ)) (closedBall ((Real.pi : ℂ)*n) r) = 1 ∧
          ∀ z ∈ sphere ((Real.pi : ℂ)*n) r, deriv (canonicalDiscriminant hp ψ) z ≠ 0) ∧
        (∀ K : ℕ, N ≤ K →
          analyticZeroCount (deriv (canonicalDiscriminant hp ψ)) (closedBall 0 (centralCircleRadius K)) = 2*K+1 ∧
          ∀ z ∈ sphere 0 (centralCircleRadius K), deriv (canonicalDiscriminant hp ψ) z ≠ 0) ∧
        (∀ K : ℕ, N ≤ K → ∀ z : ℂ, deriv (canonicalDiscriminant hp ψ) z = 0 →
          z ∈ ball 0 (centralCircleRadius K) ∨ ∃ n : ℤ, K < n.natAbs ∧ z ∈ ball ((Real.pi : ℂ)*n) r) := by
  obtain ⟨U, ho, hconv, hφ, h0, R, hb⟩ := exists_uniform_discriminant_derivative_rouche hp hp1 φ hr hrπ
  obtain ⟨N, hN, hmargin⟩ := exists_free_center_cutoff R r
  refine ⟨N, hN, U, ho, hconv, hφ, h0, ?_⟩
  intro ψ hψ heven
  have ha := analyticOnNhd_discriminant_derivative hp hp1 ψ heven
  have hd (n : ℤ) (hn : N ≤ n.natAbs) (z : ℂ) (hz : z ∈ sphere ((Real.pi : ℂ)*n) r) :=
    hb ψ hψ heven z (norm_ge_of_mem_freeSphere hmargin hn hz) (freeSphere_separated hr hrπ n hz)
  have hc (K : ℕ) (hK : N ≤ K) (z : ℂ) (hz : z ∈ sphere 0 (centralCircleRadius K)) :=
    hb ψ hψ heven z (by
      have hzn : ‖z‖ = centralCircleRadius K := by simpa using hz
      rw [hzn]
      exact threshold_le_centralCircleRadius hr.le hmargin hK)
      (fun n => hrπ.trans ((by linarith [Real.pi_pos] : Real.pi/4 ≤ Real.pi/2).trans (centralCircle_lattice_gap K hz n)))
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    refine ⟨?_, fun z hz => (rouche_ratio_mem_slitPlane (hd n hn z hz)).2.1⟩
    rw [analyticZeroCount_eq_of_boundary_lt hr (by intro z hz; fun_prop) (ha.mono (subset_univ _)) (hd n hn)]
    exact analyticZeroCount_free_derivative_disc hr.le (by linarith [Real.pi_pos]) n
  · intro K hK
    refine ⟨?_, fun z hz => (rouche_ratio_mem_slitPlane (hc K hK z hz)).2.1⟩
    rw [analyticZeroCount_eq_of_boundary_lt (centralCircleRadius_pos K)
      (by intro z hz; fun_prop) (ha.mono (subset_univ _)) (hc K hK)]
    exact analyticZeroCount_free_derivative_central K
  · intro K hK z hz
    exact root_mem_central_or_distant_of_exterior_ne_zero hr hrπ hmargin hK
      (fun w hw hsep => (rouche_ratio_mem_slitPlane (hb ψ hψ heven w hw hsep)).2.1) hz

/-- The complex counting and exhaustion part of Lemma 8.3 with a locally uniform cutoff. -/
theorem exists_uniform_discriminant_critical_distribution (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4) :
    ∃ N : ℕ, 0 < N ∧ ∃ U : Set (PairSpace p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U, ψ ∈ pairParitySubspace 0 →
        (∀ n : ℤ, N < n.natAbs → ∃ x ∈ ball ((Real.pi : ℂ)*n) r,
          deriv (canonicalDiscriminant hp ψ) x = 0 ∧
          analyticOrderAt (deriv (canonicalDiscriminant hp ψ)) x = 1 ∧
          ∀ z ∈ closedBall ((Real.pi : ℂ)*n) r, deriv (canonicalDiscriminant hp ψ) z = 0 ↔ z = x) ∧
        (∀ K : ℕ, N ≤ K →
          analyticZeroCount (deriv (canonicalDiscriminant hp ψ)) (closedBall 0 (centralCircleRadius K)) = 2*K+1 ∧
          ∀ z ∈ sphere 0 (centralCircleRadius K), deriv (canonicalDiscriminant hp ψ) z ≠ 0) ∧
        (∀ K : ℕ, N ≤ K → ∀ z : ℂ, deriv (canonicalDiscriminant hp ψ) z = 0 →
          z ∈ ball 0 (centralCircleRadius K) ∨ ∃ n : ℤ, K < n.natAbs ∧ z ∈ ball ((Real.pi : ℂ)*n) r) := by
  obtain ⟨N, hN, U, ho, hconv, hφ, h0, hdata⟩ := exists_uniform_discriminant_critical_counts hp hp1 φ hr hrπ
  refine ⟨N, hN, U, ho, hconv, hφ, h0, ?_⟩
  intro ψ hψ heven
  obtain ⟨hd, hc, he⟩ := hdata ψ hψ heven
  exact ⟨fun n hn => unique_simple_criticalPoint_of_count hp hp1 ψ heven _ r (hd n hn.le).1 (hd n hn.le).2,
    hc, he⟩

end NLS.ZakharovShabat
