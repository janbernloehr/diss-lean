import NLS.ZakharovShabat.PeriodicRootSequence
import NLS.ZakharovShabat.SpectralDisplacementTail

/-!
# The periodic midpoint displacement sequence

Convexity bounds each midpoint displacement power by half the sum of the
two eigenvalue displacement powers. The original contour midpoint therefore
has a convergent quantitative tail and a full ℓp displacement sequence.
-/

noncomputable section
open scoped ENNReal NNReal
namespace NLS.ZakharovShabat

/-- Convexity gives the exact factor one half for the midpoint power. -/
theorem norm_midpoint_displacement_rpow_le {P : ℝ} (hP : 1 ≤ P) (x y c : ℂ) :
    ‖(x+y)/2-c‖^P ≤ (‖x-c‖^P+‖y-c‖^P)/2 := by
  have hn : ‖(x+y)/2-c‖ ≤ (‖x-c‖+‖y-c‖)/2 := by
    rw [show (x+y)/2-c = ((x-c)+(y-c))/2 by ring, norm_div]
    norm_num
    exact div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
  have hm : ((1/2 : ℝ)*‖x-c‖+(1/2 : ℝ)*‖y-c‖)^P ≤
      (1/2 : ℝ)*‖x-c‖^P+(1/2 : ℝ)*‖y-c‖^P := by
    exact_mod_cast NNReal.rpow_arith_mean_le_arith_mean2_rpow (1/2) (1/2)
      (⟨‖x-c‖,norm_nonneg _⟩ : ℝ≥0) (⟨‖y-c‖,norm_nonneg _⟩ : ℝ≥0) (by norm_num) hP
  have hb := Real.rpow_le_rpow (norm_nonneg _) hn (zero_le_one.trans hP)
  have he : (‖x-c‖+‖y-c‖)/2 = (1/2 : ℝ)*‖x-c‖+(1/2 : ℝ)*‖y-c‖ := by ring
  rw [he] at hb
  linarith

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The original midpoint has a locally uniform corrected power-tail bound and a full ℓp displacement sequence. -/
theorem exists_uniform_periodicMidpointSummability (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U,
        Memℓp (fun n : ℤ => periodicMidpoint hp (weightedBaseToPair w ψ) n-(Real.pi : ℂ)*n) p ∧
        ∀ N : ℕ, N₀ ≤ N →
          Summable (spectralDisplacementPowerTail p N (periodicMidpoint hp (weightedBaseToPair w ψ))) ∧
          (∑' n : ℤ, spectralDisplacementPowerTail p N (periodicMidpoint hp (weightedBaseToPair w ψ)) n) ≤
            rootDisplacementBudget w ψ N / 2 := by
  obtain ⟨N₀,hN₀,U,ho,hc,hφ,h0,hroots⟩ := exists_uniform_periodicRoots_with_power_sums hp hp1 w φ
  have hP : 1 ≤ p.toReal := (ENNReal.toReal_le_toReal (by simp) hp).mpr (show 1 ≤ p from Fact.out)
  refine ⟨N₀,hN₀,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ
  obtain ⟨ξ,η,hpair,htail⟩ := hroots ψ hψ
  have hs (N : ℕ) (hN : N₀ ≤ N) :
      Summable (spectralDisplacementPowerTail p N (periodicMidpoint hp (weightedBaseToPair w ψ))) ∧
      (∑' n : ℤ, spectralDisplacementPowerTail p N (periodicMidpoint hp (weightedBaseToPair w ψ)) n) ≤
        rootDisplacementBudget w ψ N / 2 := by
    have hb (n : ℤ) : spectralDisplacementPowerTail p N (periodicMidpoint hp (weightedBaseToPair w ψ)) n ≤
        (1/2 : ℝ)*rootDisplacementPowerTail p N ξ η n := by
      unfold spectralDisplacementPowerTail rootDisplacementPowerTail
      by_cases hn : N ≤ n.natAbs
      · simp only [if_pos hn, (hpair n (hN.trans hn)).midpoint_eq]
        convert norm_midpoint_displacement_rpow_le hP (ξ n) (η n) ((Real.pi : ℂ)*n) using 1
        ring
      · simp only [if_neg hn, mul_zero, le_refl]
    obtain ⟨ha,hb'⟩ := spectralDisplacementPowerTail_summable_and_le p N _ _
      ((htail N hN).1.mul_left (1/2)) hb
    rw [tsum_mul_left] at hb'
    exact ⟨ha,hb'.trans (by linarith [(htail N hN).2.1])⟩
  exact ⟨memℓp_displacement_of_summable_tail (zero_lt_one.trans_le hP) N₀ _ (hs N₀ le_rfl).1,hs⟩

end NLS.ZakharovShabat
