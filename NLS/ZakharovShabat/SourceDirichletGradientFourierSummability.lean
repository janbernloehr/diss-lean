import NLS.ZakharovShabat.SourceDirichletGradientTimeBounds
import NLS.ZakharovShabat.ClassicalDirichletGradientFourier
import NLS.ZakharovShabat.ClassicalEndpointGradientFiniteSummability

/-! # Fourier summability of the actual-root Dirichlet gradient error

One summable tail majorant works on a source neighborhood and a physical H¹
ball. Each fixed source has full-sequence summability, including its finite
head. Identification with the actual cotangent uses the previously proved
common simple-root domain; no such restriction is needed for the total
normalized physical expression considered here.
-/

noncomputable section
open Set NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A single outer ℓˢ majorant controls the Fourier error tails for every
contractive scalar observation, uniformly on nearby physical H¹ sources. -/
theorem exists_local_source_dirichlet_gradient_fourier_tail_majorant
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (s : ℝ) (hs : 1 < s) (q : ℝ≥0∞) (hq : ENNReal.ofReal (1+1/s) < q)
    (ψ₀ : CoeffPair p) (M : ℝ) (hM : 0 ≤ M) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ ψ₀ ∈ U ∧ ∃ N : ℕ, 0 < N ∧
      ∃ b : ℤ → ℝ, Memℓp b (ENNReal.ofReal s) ∧
      ∀ (φ : CoeffPair 2), CoeffPair.exponentInclusion h2p φ ∈ U →
      ∀ (a : Domain 2), ‖a‖ ≤ M → periodOnePotential φ = domainInclusion a →
      ∀ (P : (ℂ × ℂ) →L[ℝ] ℂ), ‖P‖ ≤ 1 → ∀ n : ℤ, N ≤ n.natAbs →
        ‖classicalDirichletGradientFourierCoefficients
          (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq)
          (classicalSobolevPotential a)
          (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (CoeffPair.exponentInclusion h2p φ) n)
          ((Real.pi : ℂ)*n) P‖ ≤ b n := by
  obtain ⟨U,hU,hψ,N,hN,A,D,hA,hD,hbounds⟩ :=
    exists_local_source_dirichlet_gradient_time_bounds hp hp1 h2p ψ₀ M hM
  obtain ⟨K,α,_,hα,hpower⟩ := exists_classicalDirichletGradientFourier_power_bound s hs q hq A D hA hD
  refine ⟨U,hU,hψ,N,hN,(fun n => K*(n.natAbs : ℝ)^(-α)),
    (memlp_inverse_natAbs_rpow s (by linarith) α hα).const_mul K,?_⟩
  intro φ hφ a ha hcompat P hP n hn
  have hn1 : 1 ≤ (n.natAbs : ℝ) := by exact_mod_cast hN.trans_le hn
  exact hpower _ _ _ P hP _ hn1
    (fun t => (hbounds φ hφ a ha hcompat n hn t).1)
    (fun t => (hbounds φ hφ a ha hcompat n hn t).2)

/-- The actual normalized physical gradient error has ℓˢ Fourier norms at
every H¹ source. Its unrestricted finite head is included. -/
theorem memlp_source_dirichlet_gradient_fourier_norms
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (s : ℝ) (hs : 1 < s) (q : ℝ≥0∞) (hq : ENNReal.ofReal (1+1/s) < q)
    (φ : CoeffPair 2) (a : Domain 2) (hcompat : periodOnePotential φ = domainInclusion a)
    (P : (ℂ × ℂ) →L[ℝ] ℂ) (hP : ‖P‖ ≤ 1) :
    Memℓp (fun n : ℤ => ‖classicalDirichletGradientFourierCoefficients
      (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq)
      (classicalSobolevPotential a)
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (CoeffPair.exponentInclusion h2p φ) n)
      ((Real.pi : ℂ)*n) P‖) (ENNReal.ofReal s) := by
  let : Fact (1 ≤ q) := ⟨(ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))).trans hq.le⟩
  obtain ⟨U,_,hφ,N,_,b,hb,hbound⟩ := exists_local_source_dirichlet_gradient_fourier_tail_majorant
    hp hp1 h2p s hs q hq (CoeffPair.exponentInclusion h2p φ) ‖a‖ (norm_nonneg a)
  apply memlp_of_natAbs_eventual_bound s (by linarith) _ b hb N
  intro n hn
  simpa only [norm_norm] using hbound φ hφ a le_rfl hcompat P hP n hn

/-- In particular, the physical error's conjugate-exponent Fourier norms
form an outer ℓᵖ sequence for every finite source exponent p≥2. -/
theorem memlp_source_dirichlet_gradient_conjugate_fourier_norms
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ : CoeffPair 2) (a : Domain 2) (hcompat : periodOnePotential φ = domainInclusion a)
    (P : (ℂ × ℂ) →L[ℝ] ℂ) (hP : ‖P‖ ≤ 1) :
    Memℓp (fun n : ℤ => ‖classicalDirichletGradientFourierCoefficients
      (q := ENNReal.ofReal (p.toReal/(p.toReal-1)))
      (ENNReal.one_lt_ofReal.mpr (by
        have hpR : 1 < p.toReal := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
        apply (lt_div_iff₀ (by linarith : 0 < p.toReal-1)).mpr
        linarith))
      (classicalSobolevPotential a)
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet (CoeffPair.exponentInclusion h2p φ) n)
      ((Real.pi : ℂ)*n) P‖) p := by
  have hpR : 1 < p.toReal := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
  have h := memlp_source_dirichlet_gradient_fourier_norms hp hp1 h2p p.toReal hpR _
    (conjugate_exponent_ennreal_gt_gradient_threshold p.toReal hpR) φ a hcompat P hP
  simpa only [ENNReal.ofReal_toReal hp] using h

end NLS.ZakharovShabat
