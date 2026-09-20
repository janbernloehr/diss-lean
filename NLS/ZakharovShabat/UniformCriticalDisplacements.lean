import NLS.ZakharovShabat.CriticalPointMultiplicity
import NLS.ZakharovShabat.CriticalDisplacementBound
import NLS.ZakharovShabat.UniformCriticalCounts

/-!
# Lemma 8.5: locally uniform lp critical-point displacements

A common neighborhood supplies the counted central and distant critical
points and the sampled derivative-error majorant. Every completed labeling
has bounded lp displacement, with its actual central analytic multiplicities
retained. Ordering, continuity, and the derivative product are separate steps.
-/

noncomputable section
open Set Complex Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Complete actual critical-point labels have uniformly bounded lp displacement near each potential. -/
theorem exists_uniform_critical_displacements (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p) :
    ∃ N : ℕ, 0 < N ∧ ∃ U : Set (PairSpace p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∃ R : ℝ, 0 ≤ R ∧
        ∀ ψ ∈ U, ∀ hψ : ψ ∈ pairParitySubspace 0,
          ∃ ξ : ℤ → ℂ, ∃ a : Coeff p, CriticalPointLabeling hp hp1 ψ hψ N ξ ∧
            (∀ n, ξ n = (Real.pi : ℂ)*n+a n) ∧ ‖a‖ ≤ R := by
  obtain ⟨N, hN, Uc, hoc, hcc, hφc, h0c, hc⟩ := exists_uniform_discriminant_critical_distribution hp hp1 φ
    (by positivity : 0 < Real.pi/4) le_rfl
  obtain ⟨Ua, hoa, hca, hφa, h0a, K, hK, ha⟩ := exists_uniform_discriminant_value_derivative_majorants hp hp1 φ
  obtain ⟨C, hC, hs⟩ := exists_freeDisc_sine_displacement_bound (by linarith [Real.pi_pos] : Real.pi/4 < Real.pi)
  let B := centralCircleRadius N+Real.pi*N
  let R := (Finset.Icc (-(N : ℤ)) N).card*B+(C*2/Real.pi)*K
  have hB : 0 ≤ B := add_nonneg (centralCircleRadius_pos N).le (by positivity)
  refine ⟨N, hN, Uc ∩ Ua, hoc.inter hoa, hcc.inter hca, ⟨hφc, hφa⟩, ⟨h0c, h0a⟩,
    R, by dsimp [R]; positivity, fun ψ hψ heven => ?_⟩
  obtain ⟨hd, hcentral, he⟩ := hc ψ hψ.1 heven
  obtain ⟨ξ, hξ⟩ := exists_criticalPointLabeling hp hp1 ψ heven N hd (hcentral N le_rfl).1 (he N le_rfl)
  obtain ⟨A, hA, hb⟩ := ha ψ hψ.2 heven
  obtain ⟨a, heq, hanorm⟩ := exists_criticalDisplacementCoeff_le hC hs hp ψ A N ξ
    (norm_centralCriticalLabel_displacement_le hp hp1 ψ heven N ξ hξ.central)
    (fun n hn => by
      have h := (hξ.distant n hn).1
      exact (show ‖ξ n-(Real.pi : ℂ)*n‖ < Real.pi/4 by simpa only [mem_ball, dist_eq_norm] using h).le)
    (fun n hn => (hξ.distant n hn).2.1) (fun n z hz => (hb n z hz).2)
  refine ⟨ξ, a, hξ, fun n => ?_, hanorm.trans ?_⟩
  · rw [heq]
    ring
  · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hA (by positivity))

/-- At each potential the complete critical root sequence has an lp displacement from the free lattice. -/
theorem exists_criticalPointLabeling_memℓp (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) :
    ∃ N : ℕ, ∃ ξ : ℤ → ℂ, CriticalPointLabeling hp hp1 φ hφ N ξ ∧
      Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p := by
  obtain ⟨N, _, _, _, _, hmem, _, _, _, h⟩ := exists_uniform_critical_displacements hp hp1 φ
  obtain ⟨ξ, a, hξ, ha, _⟩ := h φ hmem hφ
  refine ⟨N, ξ, hξ, ?_⟩
  have hm : Memℓp (fun n => a n) p := lp.memℓp a
  simpa only [ha, add_sub_cancel_left] using hm

end NLS.ZakharovShabat
