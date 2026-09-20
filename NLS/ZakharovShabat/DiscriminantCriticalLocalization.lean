import NLS.ZakharovShabat.DiscriminantDerivativeRatio
import NLS.ComplexAnalysis.AnalyticZeroCount
import NLS.ComplexAnalysis.AnalyticQuotientUniqueness

/-!
# Initial localization and discreteness of discriminant critical points

At each fixed even potential, every sufficiently large critical point lies
in a free disc of any prescribed positive radius at most pi/4. The derivative
is a nontrivial entire function, so its zeros have finite orders and are finite
on compact sets. Counts and labels of individual critical points remain separate.
-/

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The spectral derivative of the intrinsic discriminant is entire. -/
theorem analyticOnNhd_discriminant_derivative (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) :
    AnalyticOnNhd ℂ (deriv (canonicalDiscriminant hp φ)) univ :=
  (analyticOnNhd_canonicalDiscriminant hp hp1 φ hφ).deriv

/-- The spectral derivative cannot vanish at sufficiently large separated parameters. -/
theorem exists_threshold_discriminant_derivative_ne_zero (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4) :
    ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → (∀ n : ℤ, r ≤ ‖z-(Real.pi : ℂ)*n‖) →
      deriv (canonicalDiscriminant hp φ) z ≠ 0 := by
  obtain ⟨R, hR⟩ := exists_threshold_discriminant_derivative_div_free hp hp1 φ hφ hr hrπ
    (by norm_num : (0 : ℝ) < 1/2)
  refine ⟨R, ?_⟩
  intro z hz hsep he
  have h := hR z hz hsep
  simp only [he, zero_div, zero_sub, norm_neg, norm_one] at h
  norm_num at h

/-- Every sufficiently large critical point lies inside a prescribed free disc. -/
theorem exists_threshold_critical_mem_freeDisc (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4) :
    ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → deriv (canonicalDiscriminant hp φ) z = 0 →
      ∃ n : ℤ, ‖z-(Real.pi : ℂ)*n‖ < r := by
  obtain ⟨R, hR⟩ := exists_threshold_discriminant_derivative_ne_zero hp hp1 φ hφ hr hrπ
  refine ⟨R, ?_⟩
  intro z hz he
  by_contra h
  push Not at h
  exact hR z hz h he

/-- The derivative has a nonzero value on the real cosine-zero sequence. -/
theorem exists_discriminant_derivative_ne_zero (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) :
    ∃ n : ℕ, deriv (canonicalDiscriminant hp φ) (freeCosineZero n) ≠ 0 := by
  obtain ⟨R, hR⟩ := exists_threshold_discriminant_derivative_ne_zero hp hp1 φ hφ
    (by positivity : 0 < Real.pi/4) le_rfl
  obtain ⟨n, hn⟩ := (tendsto_norm_freeCosineZero.eventually_ge_atTop R).exists
  exact ⟨n, hR _ hn (freeCosineZero_separated n)⟩

/-- Critical-point multiplicities are finite at every spectral parameter. -/
theorem analyticOrderAt_discriminant_derivative_ne_top (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) (z : ℂ) :
    analyticOrderAt (deriv (canonicalDiscriminant hp φ)) z ≠ ⊤ := by
  obtain ⟨n, hn⟩ := exists_discriminant_derivative_ne_zero hp hp1 φ hφ
  exact NLS.ComplexAnalysis.analyticOrderAt_ne_top_on_connected isPreconnected_univ
    (analyticOnNhd_discriminant_derivative hp hp1 φ hφ) (mem_univ _) hn (mem_univ z)

/-- Every spectral point has a punctured neighborhood containing no critical points. -/
theorem eventually_discriminant_derivative_ne_zero (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, deriv (canonicalDiscriminant hp φ) w ≠ 0 :=
  NLS.ComplexAnalysis.eventually_ne_zero_of_finite_analyticOrder
    (analyticOnNhd_discriminant_derivative hp hp1 φ hφ z (mem_univ _))
    (analyticOrderAt_discriminant_derivative_ne_top hp hp1 φ hφ z)

/-- Any compact spectral set contains only finitely many critical points. -/
theorem finite_discriminant_criticalPoints_of_isCompact (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) {K : Set ℂ} (hK : IsCompact K) :
    (K ∩ {z | deriv (canonicalDiscriminant hp φ) z = 0}).Finite := by
  obtain ⟨n, hn⟩ := exists_discriminant_derivative_ne_zero hp hp1 φ hφ
  have hc := (analyticOnNhd_discriminant_derivative hp hp1 φ hφ).preimage_zero_mem_codiscrete hn
  have hm : codiscreteWithin K ≤ codiscrete ℂ := codiscreteWithin_mono (subset_univ K)
  have hf := hK.finite_sdiff_of_mem_codiscreteWithin (hm hc)
  have he : deriv (canonicalDiscriminant hp φ) ⁻¹' {0} =
      {z | deriv (canonicalDiscriminant hp φ) z = 0} := by ext z; simp
  simpa only [sdiff_eq, ← preimage_compl, compl_compl, he] using hf

/-- At zero potential the intrinsic derivative is exactly the free derivative. -/
theorem discriminant_derivative_zero (hp : p ≠ ⊤) (z : ℂ) :
    deriv (canonicalDiscriminant hp (0 : PairSpace p)) z = -2*sin z := by
  rw [show canonicalDiscriminant hp (0 : PairSpace p) = freeDiscriminant from
    funext (canonicalDiscriminant_zero_finite hp)]
  exact (hasDerivAt_freeDiscriminant z).deriv

/-- The free critical points are exactly the free spectral lattice. -/
theorem discriminant_derivative_zero_eq_zero_iff (hp : p ≠ ⊤) (z : ℂ) :
    deriv (canonicalDiscriminant hp (0 : PairSpace p)) z = 0 ↔ z ∈ freeLattice := by
  rw [discriminant_derivative_zero]
  constructor
  · intro h
    have hs : sin z = 0 := (mul_eq_zero.mp h).resolve_left (by norm_num)
    obtain ⟨n, hn⟩ := Complex.sin_eq_zero_iff.mp hs
    exact ⟨n, by simpa [mul_comm] using hn.symm⟩
  · rintro ⟨n, rfl⟩
    have hs : sin ((Real.pi : ℂ)*n) = 0 :=
      Complex.sin_eq_zero_iff.mpr ⟨n, mul_comm _ _⟩
    rw [hs, mul_zero]

end NLS.ZakharovShabat
