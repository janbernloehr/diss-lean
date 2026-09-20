import NLS.ZakharovShabat.UniformSpectralDisplacements
import NLS.ZakharovShabat.UniformPowerTail

/-!
# Locally small corrected displacement budgets

For each tolerance, one open convex potential neighborhood and one cutoff make
the corrected budget small at every larger cutoff. The neighborhood may depend
on the tolerance. The additive leading Fourier tail is retained.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The corrected paired displacement budget can be made locally uniformly small. -/
theorem exists_uniform_small_rootDisplacementBudget (hp : p ≠ ⊤) (hp1 : 1 < p)
    (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N → rootDisplacementBudget w ψ N < ε := by
  let M := ‖φ‖+1
  let A := M^p.toReal
  let C := rootDisplacementSummationConstant p * (1+(1+A)*A)
  have hpR : 1 < p.toReal := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
  have hC : 0 ≤ C := by
    have hc := rootDisplacementSummationConstant_nonneg p
    dsimp [C, A, M]
    positivity
  obtain ⟨N₀, hN₀, U, ho, hconv, hφ, h0, hnorm, hb⟩ := exists_uniform_powerTail_budget hp w φ
    (zero_lt_one.trans hpR) (by positivity : 0 < min 1 (p.toReal-1)) hC hε
  refine ⟨N₀, hN₀, U, ho, hconv, hφ, h0, ?_⟩
  intro ψ hψ N hN
  apply lt_of_le_of_lt _ (hb ψ hψ N hN)
  have hc := rootDisplacementSummationConstant_nonneg p
  have hψnorm : ‖ψ‖ ≤ M := (hnorm ψ hψ).le
  let T := ‖weightedPairFourierTail w.toWeight (N/2) ψ‖^p.toReal
  let D := (N : ℝ)^(min 1 (p.toReal-1))
  change rootDisplacementBudget w ψ N ≤ C*(A/D+T)
  calc
    _ ≤ rootDisplacementSummationConstant p * (T+(A/D+T)*(1+A)*A) := by
      unfold rootDisplacementBudget
      dsimp [T, A, D]
      gcongr
    _ ≤ rootDisplacementSummationConstant p * ((A/D+T)+(A/D+T)*(1+A)*A) := by
      gcongr
      exact le_add_of_nonneg_left (by dsimp [A, D]; positivity)
    _ = _ := by dsimp [C]; ring

/-- A paired power-tail budget controls each displacement tail in its actual lp norm. -/
theorem norm_displacement_tails_le_of_power_sum (hp : p ≠ ⊤) (N : ℕ) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p)
    (hs : Summable (rootDisplacementPowerTail p N ξ η)) {ε : ℝ} (hε : 0 ≤ ε)
    (hb : (∑' n : ℤ, rootDisplacementPowerTail p N ξ η n) ≤ ε^p.toReal) :
    ‖(⟨_,hξ⟩ : Coeff p)-Coeff.truncate (Finset.Icc (-(N : ℤ)) N) ⟨_,hξ⟩‖ ≤ ε ∧
    ‖(⟨_,hη⟩ : Coeff p)-Coeff.truncate (Finset.Icc (-(N : ℤ)) N) ⟨_,hη⟩‖ ≤ ε := by
  have hpR : 0 < p.toReal := zero_lt_one.trans_le
    ((ENNReal.toReal_le_toReal (by simp) hp).mpr (show 1 ≤ p from Fact.out))
  constructor <;> apply lp.norm_le_of_tsum_le hpR hε
  all_goals
    apply le_trans _ hb
    apply Summable.tsum_le_tsum _ _ hs
    · intro n
      by_cases hn : n ∈ Finset.Icc (-(N : ℤ)) N
      · simp only [lp.coeFn_sub, Pi.sub_apply, Coeff.truncate_apply, if_pos hn, sub_self,
          norm_zero, Real.zero_rpow hpR.ne']
        unfold rootDisplacementPowerTail
        split_ifs <;> positivity
      · have hN : N ≤ n.natAbs := by rw [Finset.mem_Icc] at hn; omega
        simp only [lp.coeFn_sub, Pi.sub_apply, Coeff.truncate_apply, if_neg hn, sub_zero,
          rootDisplacementPowerTail, if_pos hN]
        first | exact le_add_of_nonneg_right (by positivity) | exact le_add_of_nonneg_left (by positivity)
    · exact lp.memℓp _ |>.summable hpR

end NLS.ZakharovShabat
