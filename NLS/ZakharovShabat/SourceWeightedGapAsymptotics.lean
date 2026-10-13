import NLS.ZakharovShabat.PeriodicGapSummability
import NLS.ZakharovShabat.SourceResolvent
import NLS.ZakharovShabat.UniformPowerTail

/-!
# Original weighted gap asymptotics in Section 6

The weighted source norm is exactly the printed component-sum norm. Forgetting
the weight preserves every physical Fourier coefficient. The corrected gap
budget retains its additive leading Fourier tail and uses floor(N/2).
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Forget the weight into the original raw period-two pair, without doubling frequencies. -/
def sourceWeightedPeriodTwoInput (w : SpectralWeight) :
    WeightedCoeffPair w.toWeight p →L[ℂ] CoeffPair p :=
  (CoeffPair.toMax p).symm.toContinuousLinearMap.comp (weightedBaseToPair w)

@[simp] theorem sourceWeightedPeriodTwoInput_fst (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (k : ℤ) :
    (sourceWeightedPeriodTwoInput w φ).fst k = φ.fst.val k :=
  weightedBaseToPair_fst w φ k

@[simp] theorem sourceWeightedPeriodTwoInput_snd (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (k : ℤ) :
    (sourceWeightedPeriodTwoInput w φ).snd k = φ.snd.val k :=
  weightedBaseToPair_snd w φ k

theorem toMax_sourceWeightedPeriodTwoInput (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    CoeffPair.toMax p (sourceWeightedPeriodTwoInput w φ) = weightedBaseToPair w φ :=
  ContinuousLinearEquiv.apply_symm_apply _ _

/-- Weighted spectral membership is noninvertibility of the actual original source pencil. -/
theorem sourceWeightedPeriodTwoSpectrum_iff (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (z : ℂ) :
    z ∉ sourceResolventSet hp (sourceWeightedPeriodTwoInput w φ) ↔
      z ∈ periodicSpectrum hp (weightedBaseToPair w φ) := by
  rw [sourceResolventSet_eq,toMax_sourceWeightedPeriodTwoInput]
  rfl

/-- Corrected Proposition 6.3 with the original norm, actual source spectrum,
and original contour squared gap, all on one neighborhood for all larger cutoffs. -/
theorem sourceProposition6_3_corrected (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U,
        ∃ ξ η : ℤ → ℂ,
          (∀ n : ℤ, N₀ ≤ n.natAbs → PeriodicResonantPair hp w ψ n (ξ n) (η n)) ∧
          (∀ n : ℤ, N₀ ≤ n.natAbs → ∀ z ∈ resonantStrip n,
            z ∉ sourceResolventSet hp (sourceWeightedPeriodTwoInput w ψ) ↔ z = ξ n ∨ z = η n) ∧
          ∀ N : ℕ, N₀ ≤ N →
            Summable (periodicGapPowerTail hp w ψ N) ∧
            (∑' n : ℤ, periodicGapPowerTail hp w ψ N n) ≤ rootGapBudget w ψ N := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,hr⟩ := exists_uniform_periodicRoots_with_power_sums hp hp1 w φ
  refine ⟨N,hN,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ
  obtain ⟨ξ,η,hpair,ht⟩ := hr ψ hψ
  refine ⟨ξ,η,hpair,?_,?_⟩
  · intro n hn z hz
    exact (sourceWeightedPeriodTwoSpectrum_iff hp w ψ z).trans ((hpair n hn).spectrum_iff z hz)
  · intro K hK
    rw [periodicGapPowerTail_eq_rootGapPowerTail hp w ψ K ξ η
      (fun n hn => (hpair n (hK.trans hn)).squaredGap_eq)]
    exact (ht K hK).2.2

/-- The corrected weighted gap budget becomes locally uniformly small. -/
theorem exists_uniform_small_rootGapBudget (hp : p ≠ ⊤) (hp1 : 1 < p)
    (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N → rootGapBudget w ψ N < ε := by
  let A := (‖φ‖+1)^p.toReal
  let B := offDiagonalSummationConstant p
  let C := rootGapSummationConstant p * (1+B*A^2)
  have hB : 0 ≤ B := offDiagonalSummationConstant_nonneg p
  have hG := rootGapSummationConstant_nonneg p
  have hC : 0 ≤ C := by dsimp [C,A]; positivity
  have hP : 1 < p.toReal := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
  obtain ⟨N,hN,U,ho,hc,hφ,h0,hnorm,hb⟩ := exists_uniform_powerTail_budget hp w φ
    (zero_lt_one.trans hP) (by positivity : 0 < min 1 (p.toReal-1)) hC hε
  refine ⟨N,hN,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ K hK
  let T := ‖weightedPairFourierTail w.toWeight (K/2) ψ‖^p.toReal
  let D := (K : ℝ)^(min 1 (p.toReal-1))
  have hψA : ‖ψ‖^p.toReal ≤ A := Real.rpow_le_rpow (norm_nonneg _) (hnorm ψ hψ).le (by positivity)
  have hTA : T ≤ A := (Real.rpow_le_rpow (norm_nonneg _)
    (norm_weightedPairFourierTail_le hp w.toWeight (K/2) ψ) (by positivity)).trans hψA
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hpow (r : ℝ) (hr : 0 ≤ r) : r^(2*p.toReal) = (r^p.toReal)^2 := by
    rw [← Real.rpow_two, ← Real.rpow_mul hr]
    congr 1
    ring
  have hbudget : rootGapBudget w ψ K ≤ C*(A/D+T) := by
    unfold rootGapBudget
    rw [hpow _ (norm_nonneg _),hpow _ (norm_nonneg _)]
    change rootGapSummationConstant p * (T+B*‖ψ‖^p.toReal*((‖ψ‖^p.toReal)^2/D+T^2)) ≤ _
    calc
      _ ≤ rootGapSummationConstant p * (T+B*A*(A^2/D+A*T)) := by
        gcongr
        nlinarith
      _ ≤ rootGapSummationConstant p * ((A/D+T)+B*A*(A^2/D+A*T)) := by
        gcongr
        exact le_add_of_nonneg_left (div_nonneg hA hD)
      _ = _ := by dsimp [C]; ring
  exact hbudget.trans_lt (hb ψ hψ K hK)

/-- Locally uniform small weighted power tails for the intrinsic actual squared gap. -/
theorem sourceProposition6_3_small_tails (hp : p ≠ ⊤) (hp1 : 1 < p)
    (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N →
        Summable (periodicGapPowerTail hp w ψ N) ∧
        (∑' n : ℤ, periodicGapPowerTail hp w ψ N n) < ε := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,ht⟩ := exists_uniform_periodicGapSummability hp hp1 w φ
  obtain ⟨M,_,V,hVo,hVc,hVφ,hV0,hb⟩ := exists_uniform_small_rootGapBudget hp hp1 w φ hε
  refine ⟨max N M,hN.trans (le_max_left _ _),U ∩ V,ho.inter hVo,hc.inter hVc,
    ⟨hφ,hVφ⟩,⟨h0,hV0⟩,?_⟩
  intro ψ hψ K hK
  have hs := ht ψ hψ.1 K ((le_max_left _ _).trans hK)
  exact ⟨hs.1,hs.2.trans_lt (hb ψ hψ.2 K ((le_max_right _ _).trans hK))⟩

/-- All weighted intrinsic gap powers are summable, including the finite central block. -/
theorem sourceProposition6_3_summable (hp : p ≠ ⊤) (hp1 : 1 < p)
    (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) :
    Summable (fun n : ℤ => (w (2*n))^p.toReal *
      ‖periodicSquaredGap hp (weightedBaseToPair w φ) n‖^(p.toReal/2)) := by
  obtain ⟨N,_,U,_,_,hφ,_,ht⟩ := sourceProposition6_3_small_tails hp hp1 w φ (by norm_num : (0 : ℝ) < 1)
  let F := fun n : ℤ => (w (2*n))^p.toReal *
    ‖periodicSquaredGap hp (weightedBaseToPair w φ) n‖^(p.toReal/2)
  have hf : (fun n : ℤ => if N ≤ n.natAbs then (0 : ℝ) else F n).HasFiniteSupport := by
    apply (Set.finite_Icc (-(N : ℤ)) (N : ℤ)).subset
    intro n hn
    have hh : ¬N ≤ n.natAbs := by intro h; simp [Function.mem_support,h] at hn
    constructor <;> omega
  convert (ht φ hφ N le_rfl).1.add (summable_of_hasFiniteSupport hf) using 1
  funext n
  simp only [periodicGapPowerTail,F]
  split_ifs <;> simp

/-- Any choice of square roots of the intrinsic squared gaps has the claimed weighted ℓᵖ regularity. -/
theorem sourceProposition6_3_gap_mem (hp : p ≠ ⊤) (hp1 : 1 < p)
    (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) (γ : ℤ → ℂ)
    (hγ : ∀ n, (γ n)^2 = periodicSquaredGap hp (weightedBaseToPair w φ) n) :
    Memℓp (fun n : ℤ => (w (2*n) : ℂ)*γ n) p := by
  apply (memℓp_gen_iff (ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp)).mpr
  have hs := sourceProposition6_3_summable hp hp1 w φ
  convert hs using 1
  funext n
  rw [← hγ n,norm_sq_rpow_half,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (w.toWeight.positive _),Real.mul_rpow (w.toWeight.positive _).le (norm_nonneg _)]

end NLS.ZakharovShabat
