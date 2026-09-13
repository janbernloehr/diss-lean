import NLS.ZakharovShabat.PeriodicSpectralProductExistence

/-!
# Uniform norm bounds for actual spectral displacement families

The corrected power-tail budget is bounded on norm balls. Filling the omitted
central modes with their free values gives globally bounded `ℓp` displacement
sequences on one common potential neighborhood, with the actual high pairs and
all larger counting data retained.
-/

noncomputable section
open Filter Topology Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The corrected displacement budget is bounded by an explicit expression on every norm ball. -/
theorem rootDisplacementBudget_le_of_norm_le (hp : p ≠ ⊤) (w : SpectralWeight)
    (ψ : WeightedCoeffPair w.toWeight p) (N : ℕ) (R : ℝ) (hR : 0 ≤ R) (hψ : ‖ψ‖ ≤ R) :
    rootDisplacementBudget w ψ N ≤ rootDisplacementSummationConstant p *
      (R^p.toReal+(R^p.toReal/(N : ℝ)^(min 1 (p.toReal-1))+R^p.toReal)*(1+R^p.toReal)*R^p.toReal) := by
  have ht : ‖weightedPairFourierTail w.toWeight (N/2) ψ‖ ≤ R :=
    (norm_weightedPairFourierTail_le hp w.toWeight (N/2) ψ).trans hψ
  have hC := rootDisplacementSummationConstant_nonneg p
  unfold rootDisplacementBudget
  gcongr

/-- A bounded paired power tail gives a common norm bound after the omitted central entries are filled freely. -/
theorem norm_completed_displacements_le (hp : p ≠ ⊤) (N : ℕ) (ξ η : ℤ → ℂ)
    (hs : Summable (rootDisplacementPowerTail p N ξ η)) (B : ℝ)
    (hb : (∑' n : ℤ, rootDisplacementPowerTail p N ξ η n) ≤ B) :
    ∃ hξ : Memℓp (fun n => centralFreeCompletion N ξ n-(Real.pi : ℂ)*n) p,
    ∃ hη : Memℓp (fun n => centralFreeCompletion N η n-(Real.pi : ℂ)*n) p,
      ‖(⟨_,hξ⟩ : Coeff p)‖ ≤ max 1 B ∧ ‖(⟨_,hη⟩ : Coeff p)‖ ≤ max 1 B := by
  have hP : 1 ≤ p.toReal := (ENNReal.toReal_le_toReal (by simp) hp).mpr (show 1 ≤ p from Fact.out)
  have hP0 := zero_lt_one.trans_le hP
  obtain ⟨hξ,hη⟩ := memℓp_pair_displacements_of_summable_tail hp N ξ η hs
  let hα := memℓp_centralFreeCompletion N ξ hξ
  let hβ := memℓp_centralFreeCompletion N η hη
  have bound (α : ℤ → ℂ) (hα : Memℓp (fun n => centralFreeCompletion N α n-(Real.pi : ℂ)*n) p)
      (hpoint : ∀ n, ‖centralFreeCompletion N α n-(Real.pi : ℂ)*n‖^p.toReal ≤
        rootDisplacementPowerTail p N ξ η n) : ‖(⟨_,hα⟩ : Coeff p)‖ ≤ max 1 B := by
    apply lp.norm_le_of_tsum_le hP0 (zero_le_one.trans (le_max_left _ _))
    exact ((hα.summable hP0).tsum_le_tsum hpoint hs).trans
      (hb.trans ((le_max_right _ _).trans (Real.self_le_rpow_of_one_le (le_max_left _ _) hP)))
  refine ⟨hα,hβ,bound ξ hα ?_,bound η hβ ?_⟩
  all_goals
    intro n
    by_cases hn : N < n.natAbs
    · simp only [centralFreeCompletion, if_pos hn, rootDisplacementPowerTail, if_pos hn.le]
      first
      | exact le_add_of_nonneg_right (by positivity)
      | exact le_add_of_nonneg_left (by positivity)
    · simp only [centralFreeCompletion, if_neg hn, sub_self, norm_zero, Real.zero_rpow hP0.ne']
      unfold rootDisplacementPowerTail
      split_ifs <;> positivity

/-- Actual counted high pairs have uniformly bounded global displacement norms on one neighborhood.
The low entries are free placeholders; the actual central polynomial retains their spectral data. -/
theorem exists_uniform_bounded_periodicDisplacements (hp : p ≠ ⊤) (hp1 : 1 < p)
    (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∃ R : ℝ, 0 ≤ R ∧ ∀ ψ ∈ U,
        ∃ ξ η : ℤ → ℂ,
        ∃ hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p,
        ∃ hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p,
          ‖(⟨_,hξ⟩ : Coeff p)‖ ≤ R ∧ ‖(⟨_,hη⟩ : Coeff p)‖ ≤ R ∧
          (∀ n : ℤ, n.natAbs ≤ N₀ → ξ n = (Real.pi : ℂ)*n ∧ η n = (Real.pi : ℂ)*n) ∧
          (∀ n : ℤ, N₀ < n.natAbs → PeriodicResonantPair hp w ψ n (ξ n) (η n)) ∧
          ∀ N ≥ N₀, PeriodicCountingData hp (weightedBaseToPair w ψ) N := by
  obtain ⟨Nr,hNr,Ur,hor,hcr,hφr,h0r,hroots⟩ := exists_uniform_periodicRoots_with_power_sums hp hp1 w φ
  obtain ⟨Nc,Uc,_,hoc,hcc,hφc,h0c,_,_,hcount⟩ := exists_uniform_periodicCountingData hp (weightedBaseToPair w φ)
  let N₀ := max Nr Nc
  let V := (weightedBaseToPair (p := p) w) ⁻¹' Uc
  have hoV : IsOpen V := hoc.preimage (weightedBaseToPair w).continuous
  have hcV : Convex ℝ V := hcc.linear_preimage ((weightedBaseToPair (p := p) w).restrictScalars ℝ).toLinearMap
  let T := ‖φ‖+1
  have hT : 0 < T := by dsimp [T]; positivity
  let U := (Ur ∩ V) ∩ ball 0 T
  let B := rootDisplacementSummationConstant p *
    (T^p.toReal+(T^p.toReal/(N₀ : ℝ)^(min 1 (p.toReal-1))+T^p.toReal)*(1+T^p.toReal)*T^p.toReal)
  refine ⟨N₀,hNr.trans (le_max_left _ _),U,(hor.inter hoV).inter isOpen_ball,
    (hcr.inter hcV).inter (convex_ball 0 T),⟨⟨hφr,hφc⟩,?_⟩,
    ⟨⟨h0r,?_⟩,mem_ball_self hT⟩,max 1 B,zero_le_one.trans (le_max_left _ _),?_⟩
  · simpa only [mem_ball, dist_zero_right, T] using lt_add_one ‖φ‖
  · simpa [V] using h0c
  · intro ψ hψ
    obtain ⟨ξ,η,hr,htail⟩ := hroots ψ hψ.1.1
    have hs := htail N₀ (le_max_left _ _)
    have hb : (∑' n : ℤ, rootDisplacementPowerTail p N₀ ξ η n) ≤ B :=
      hs.2.1.trans (rootDisplacementBudget_le_of_norm_le hp w ψ N₀ T hT.le
        (by
          have hnorm : ‖ψ‖ < T := by simpa only [mem_ball, dist_zero_right] using hψ.2
          exact hnorm.le))
    obtain ⟨hξ,hη,hξb,hηb⟩ := norm_completed_displacements_le hp N₀ ξ η hs.1 B hb
    refine ⟨centralFreeCompletion N₀ ξ,centralFreeCompletion N₀ η,hξ,hη,hξb,hηb,?_,?_,?_⟩
    · intro n hn
      simp only [centralFreeCompletion, if_neg (not_lt.mpr hn), and_self]
    · intro n hn
      simp only [centralFreeCompletion, if_pos hn]
      exact hr n ((le_max_left Nr Nc).trans hn.le)
    · intro N hN
      exact hcount (weightedBaseToPair w ψ) hψ.1.2 N ((le_max_right _ _).trans hN)

end NLS.ZakharovShabat
