import NLS.KdV.HillFiniteGapDirichletInterpolation

/-! # Exact actual finite-gap Dirichlet contour moments -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- Actual simple-root residues, including the selected closed-gap index. -/
def hillDirichletResidueMoment (n : ℕ) (hn : 1≤n) (N l : ℕ) : ℂ :=
  ∑ j ∈ Finset.range N,
    (hillDirichletEnergySequence q hq hr j : ℂ)^l*
      (hillAbelianSelectedGlobalPsi q hq hr n hn (hillDirichletEnergySequence q hq hr j)/
        deriv (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q)) (hillDirichletEnergySequence q hq hr j))

/-- An analytic test function pairs with the actual finite simple-root
residues. Neither a canonical product nor a leading scalar is postulated. -/
theorem circleIntegral_hillFiniteGapDirichlet_analytic_test
    (n N : ℕ) (hn : 1≤n) (hnN : n≤N)
    (hclosed : ∀ (k : ℕ) (_hk : 1≤k), N<k → hillRealGapHalfLength q hq hr k=0)
    (c : ℂ) (r : ℝ) (hrp : 0<r)
    (hinside : ∀ j∈Finset.range N, (hillDirichletEnergySequence q hq hr j : ℂ)∈ball c r)
    (hD : ∀ w∈sphere c r, hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) w≠0)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (closedBall c r)) :
    (∮ w in C(c,r), f w*(hillAbelianSelectedGlobalPsi q hq hr n hn w/
      hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) w))=
      (2*Real.pi*I)*∑ j ∈ Finset.range N,
        f (hillDirichletEnergySequence q hq hr j)*
          (hillAbelianSelectedGlobalPsi q hq hr n hn (hillDirichletEnergySequence q hq hr j)/
            deriv (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q)) (hillDirichletEnergySequence q hq hr j)) := by
  let μ : ℕ → ℂ := fun j => hillDirichletEnergySequence q hq hr j
  let a : ℕ → ℂ := fun j => hillAbelianSelectedGlobalPsi q hq hr n hn (μ j)/
    deriv (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q)) (μ j)
  have hi (j : ℕ) (hj : j∈Finset.range N) : CircleIntegrable (fun w : ℂ => f w*(a j/(w-μ j))) c r := by
    apply ContinuousOn.circleIntegrable hrp.le
    intro w hw
    have hne : w-μ j≠0 := sub_ne_zero.mpr (sphere_disjoint_ball.ne_of_mem hw (hinside j hj))
    exact ((hf w (sphere_subset_closedBall hw)).mul
      (analyticAt_const.div (analyticAt_id.sub analyticAt_const) hne)).continuousAt.continuousWithinAt
  calc
    _ = ∮ w in C(c,r), ∑ j ∈ Finset.range N, f w*(a j/(w-μ j)) := by
      apply circleIntegral.integral_congr hrp.le
      intro w hw
      dsimp only
      rw [hillAbelianSelectedGlobalPsi_div_dirichlet_finite_gap q hq hr n N hn hnN hclosed w (hD w hw)]
      simp only [hillDirichletInterpolationPrincipalSum,Finset.mul_sum]
      rfl
    _ = ∑ j ∈ Finset.range N, ∮ w in C(c,r), f w*(a j/(w-μ j)) := circleIntegral.integral_fun_sum hi
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have htest : DifferentiableOn ℂ (fun w => f w*a j) (closedBall c r) :=
        (show AnalyticOnNhd ℂ (fun w => f w*a j) (closedBall c r) from
          fun w hw => (hf w hw).mul analyticAt_const).differentiableOn
      have he := htest.circleIntegral_sub_inv_smul (hinside j hj)
      simpa only [smul_eq_mul,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,μ,a] using he

/-- The actual selected numerator quotient has its exact polynomial
moments on every sufficiently large selected energy circle. -/
theorem eventually_circleIntegral_hillFiniteGapDirichlet_analytic_test
    (n N : ℕ) (hn : 1≤n) (hnN : n≤N)
    (hclosed : ∀ (k : ℕ) (_hk : 1≤k), N<k → hillRealGapHalfLength q hq hr k=0)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f univ) :
    ∀ᶠ M : ℕ in atTop,
      (∮ w in C(0,(centralCircleRadius M)^2), f w*
        (hillAbelianSelectedGlobalPsi q hq hr n hn w/
          hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) w))=
        (2*Real.pi*I)*∑ j ∈ Finset.range N,
          f (hillDirichletEnergySequence q hq hr j)*
            (hillAbelianSelectedGlobalPsi q hq hr n hn (hillDirichletEnergySequence q hq hr j)/
              deriv (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q)) (hillDirichletEnergySequence q hq hr j)) := by
  obtain ⟨K,hK⟩ := eventually_hillDirichlet_sequence_circle_selection q hq hr
  filter_upwards [eventually_ge_atTop (max K N)] with M hM
  have hinside : ∀ j∈Finset.range N, (hillDirichletEnergySequence q hq hr j : ℂ)∈ball (0:ℂ) ((centralCircleRadius M)^2) := by
    intro j hj
    exact ((hK M (by omega)).1 j).mpr (by have := Finset.mem_range.mp hj;omega)
  have hD : ∀ w∈sphere (0:ℂ) ((centralCircleRadius M)^2),
      hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) w≠0 := by
    intro w hw hz
    obtain ⟨j,hj,rfl⟩ := ((hK M (by omega)).2 w (sphere_subset_closedBall hw)).mp hz
    exact sphere_disjoint_ball.ne_of_mem hw (((hK M (by omega)).1 j).mpr hj) rfl
  exact circleIntegral_hillFiniteGapDirichlet_analytic_test q hq hr n N hn hnN hclosed
    0 ((centralCircleRadius M)^2) (sq_pos_of_pos (centralCircleRadius_pos M)) hinside hD
    f (hf.mono (subset_univ _))

/-- The actual selected numerator quotient has its exact polynomial
moments on every sufficiently large selected energy circle. -/
theorem eventually_circleIntegral_hillFiniteGapDirichlet_moment
    (n N : ℕ) (hn : 1≤n) (hnN : n≤N)
    (hclosed : ∀ (k : ℕ) (_hk : 1≤k), N<k → hillRealGapHalfLength q hq hr k=0) (l : ℕ) :
    ∀ᶠ M : ℕ in atTop,
      (∮ w in C(0,(centralCircleRadius M)^2), w^l*
        (hillAbelianSelectedGlobalPsi q hq hr n hn w/
          hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) w))=
        (2*Real.pi*I)*hillDirichletResidueMoment q hq hr n hn N l := by
  exact eventually_circleIntegral_hillFiniteGapDirichlet_analytic_test q hq hr n N hn hnN hclosed
    (fun w : ℂ => w^l) (fun _ _ => analyticAt_id.pow l)

/-- Changing a valid finite-gap cutoff does not change any actual residue
moment, provided both cutoffs include the selected index. -/
theorem hillDirichletResidueMoment_cutoff_independent
    (n N₁ N₂ : ℕ) (hn : 1≤n) (hn₁ : n≤N₁) (hn₂ : n≤N₂)
    (hc₁ : ∀ (k : ℕ) (_hk : 1≤k), N₁<k → hillRealGapHalfLength q hq hr k=0)
    (hc₂ : ∀ (k : ℕ) (_hk : 1≤k), N₂<k → hillRealGapHalfLength q hq hr k=0) (l : ℕ) :
    hillDirichletResidueMoment q hq hr n hn N₁ l=hillDirichletResidueMoment q hq hr n hn N₂ l := by
  have h1 := eventually_circleIntegral_hillFiniteGapDirichlet_moment q hq hr n N₁ hn hn₁ hc₁ l
  have h2 := eventually_circleIntegral_hillFiniteGapDirichlet_moment q hq hr n N₂ hn hn₂ hc₂ l
  obtain ⟨M,hM⟩ := (h1.and h2).exists
  have hne : (2*Real.pi*I : ℂ)≠0 := mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  exact mul_left_cancel₀ hne (hM.1.symm.trans hM.2)

end NLS.KdV
