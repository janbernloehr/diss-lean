import NLS.KdV.HillFiniteGapDirichletMoments

/-! # Actual finite Dirichlet Laurent coefficients and uniform remainders -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

private theorem norm_simplePole_laurent_tail_weighted (a μ w : ℂ) (L : ℕ)
    (hw : 0<‖w‖) (hμ : 2*‖μ‖≤‖w‖) :
    ‖w‖^(L+1)*‖μ^L*a/(w^L*(w-μ))‖≤2*‖μ‖^L*‖a‖ := by
  have hdiff : ‖w‖/2≤‖w-μ‖ := by have := norm_sub_norm_le w μ;linarith
  have hdpos : 0<‖w-μ‖ := by linarith
  have hc : ‖w‖/‖w-μ‖≤2 := (div_le_iff₀ hdpos).mpr (by linarith)
  calc
    _ = (‖w‖/‖w-μ‖)*(‖μ‖^L*‖a‖) := by
      rw [norm_div,norm_mul,norm_mul,norm_pow,norm_pow,pow_succ]
      field_simp
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hc (mul_nonneg (pow_nonneg (norm_nonneg μ) L) (norm_nonneg a))]

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem hillDirichletPrincipalSum_laurent_two (n : ℕ) (hn : 1≤n) (N : ℕ)
    (w : ℂ) (hw : w≠0)
    (hD : hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) w≠0) :
    hillDirichletInterpolationPrincipalSum q hq hr n hn N w-
      hillDirichletResidueMoment q hq hr n hn N 0/w-
      hillDirichletResidueMoment q hq hr n hn N 1/w^2=
      ∑ j ∈ Finset.range N,
        (hillDirichletEnergySequence q hq hr j : ℂ)^2*
          (hillAbelianSelectedGlobalPsi q hq hr n hn (hillDirichletEnergySequence q hq hr j)/
            deriv (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q)) (hillDirichletEnergySequence q hq hr j))/
              (w^2*(w-(hillDirichletEnergySequence q hq hr j : ℂ))) := by
  unfold hillDirichletInterpolationPrincipalSum hillDirichletResidueMoment
  rw [Finset.sum_div,Finset.sum_div,← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  have hz : w-(hillDirichletEnergySequence q hq hr j : ℂ)≠0 := by
    apply sub_ne_zero.mpr
    intro he
    apply hD
    rw [he]
    exact hillDirichletEnergy_zero q hq hr (j+1) (by omega)
  simp only [pow_zero,pow_one,one_mul]
  field_simp [hw,hz]
  ring

theorem exists_hillDirichletPrincipalSum_laurent_two_bound (n : ℕ) (hn : 1≤n) (N : ℕ) :
    ∃ R C : ℝ, 0<R ∧ 0<C ∧ ∀ w : ℂ, R≤‖w‖ →
      hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) w≠0 →
      ‖w‖^3*‖hillDirichletInterpolationPrincipalSum q hq hr n hn N w-
        hillDirichletResidueMoment q hq hr n hn N 0/w-
        hillDirichletResidueMoment q hq hr n hn N 1/w^2‖≤C := by
  let μ : ℕ → ℂ := fun j => hillDirichletEnergySequence q hq hr j
  let a : ℕ → ℂ := fun j => hillAbelianSelectedGlobalPsi q hq hr n hn (μ j)/
    deriv (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q)) (μ j)
  let R : ℝ := 1+2*∑ j ∈ Finset.range N, ‖μ j‖
  let C : ℝ := 1+∑ j ∈ Finset.range N, 2*‖μ j‖^2*‖a j‖
  have hR : 0<R := by dsimp only [R];positivity
  refine ⟨R,C,hR,by dsimp only [C];positivity,?_⟩
  intro w hw hD
  have hwpos : 0<‖w‖ := hR.trans_le hw
  rw [hillDirichletPrincipalSum_laurent_two q hq hr n hn N w (norm_pos_iff.mp hwpos) hD]
  calc
    _ ≤ ‖w‖^3*∑ j ∈ Finset.range N, ‖μ j^2*a j/(w^2*(w-μ j))‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = ∑ j ∈ Finset.range N, ‖w‖^3*‖μ j^2*a j/(w^2*(w-μ j))‖ := Finset.mul_sum _ _ _
    _ ≤ ∑ j ∈ Finset.range N, 2*‖μ j‖^2*‖a j‖ := by
      apply Finset.sum_le_sum
      intro j hj
      have hμ : ‖μ j‖≤∑ k ∈ Finset.range N, ‖μ k‖ :=
        Finset.single_le_sum (fun _ _ => norm_nonneg _) hj
      exact norm_simplePole_laurent_tail_weighted (a j) (μ j) w 2 hwpos (by dsimp only [R] at hw;linarith)
    _ ≤ C := by dsimp only [C];linarith

theorem hillDirichletPrincipalSum_laurent_three (n : ℕ) (hn : 1≤n) (N : ℕ)
    (w : ℂ) (hw : w≠0)
    (hD : hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) w≠0) :
    hillDirichletInterpolationPrincipalSum q hq hr n hn N w-
      hillDirichletResidueMoment q hq hr n hn N 0/w-
      hillDirichletResidueMoment q hq hr n hn N 1/w^2-
      hillDirichletResidueMoment q hq hr n hn N 2/w^3=
      ∑ j ∈ Finset.range N,
        (hillDirichletEnergySequence q hq hr j : ℂ)^3*
          (hillAbelianSelectedGlobalPsi q hq hr n hn (hillDirichletEnergySequence q hq hr j)/
            deriv (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q)) (hillDirichletEnergySequence q hq hr j))/
              (w^3*(w-(hillDirichletEnergySequence q hq hr j : ℂ))) := by
  unfold hillDirichletInterpolationPrincipalSum hillDirichletResidueMoment
  rw [Finset.sum_div,Finset.sum_div,Finset.sum_div,← Finset.sum_sub_distrib,← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  have hz : w-(hillDirichletEnergySequence q hq hr j : ℂ)≠0 := by
    apply sub_ne_zero.mpr
    intro he
    apply hD
    rw [he]
    exact hillDirichletEnergy_zero q hq hr (j+1) (by omega)
  simp only [pow_zero,pow_one,one_mul]
  field_simp [hw,hz]
  ring


theorem exists_hillDirichletPrincipalSum_laurent_three_bound (n : ℕ) (hn : 1≤n) (N : ℕ) :
    ∃ R C : ℝ, 0<R ∧ 0<C ∧ ∀ w : ℂ, R≤‖w‖ →
      hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) w≠0 →
      ‖w‖^4*‖hillDirichletInterpolationPrincipalSum q hq hr n hn N w-
        hillDirichletResidueMoment q hq hr n hn N 0/w-
        hillDirichletResidueMoment q hq hr n hn N 1/w^2-
        hillDirichletResidueMoment q hq hr n hn N 2/w^3‖≤C := by
  let μ : ℕ → ℂ := fun j => hillDirichletEnergySequence q hq hr j
  let a : ℕ → ℂ := fun j => hillAbelianSelectedGlobalPsi q hq hr n hn (μ j)/
    deriv (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q)) (μ j)
  let R : ℝ := 1+2*∑ j ∈ Finset.range N, ‖μ j‖
  let C : ℝ := 1+∑ j ∈ Finset.range N, 2*‖μ j‖^3*‖a j‖
  have hR : 0<R := by dsimp only [R];positivity
  refine ⟨R,C,hR,by dsimp only [C];positivity,?_⟩
  intro w hw hD
  have hwpos : 0<‖w‖ := hR.trans_le hw
  rw [hillDirichletPrincipalSum_laurent_three q hq hr n hn N w (norm_pos_iff.mp hwpos) hD]
  calc
    _ ≤ ‖w‖^4*∑ j ∈ Finset.range N, ‖μ j^3*a j/(w^3*(w-μ j))‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = ∑ j ∈ Finset.range N, ‖w‖^4*‖μ j^3*a j/(w^3*(w-μ j))‖ := Finset.mul_sum _ _ _
    _ ≤ ∑ j ∈ Finset.range N, 2*‖μ j‖^3*‖a j‖ := by
      apply Finset.sum_le_sum
      intro j hj
      have hμ : ‖μ j‖≤∑ k ∈ Finset.range N, ‖μ k‖ :=
        Finset.single_le_sum (fun _ _ => norm_nonneg _) hj
      exact norm_simplePole_laurent_tail_weighted (a j) (μ j) w 3 hwpos (by dsimp only [R] at hw;linarith)
    _ ≤ C := by dsimp only [C];linarith

/-- The first three actual quotient coefficients have uniform complex
large-energy remainder bounds. No normalized leading constant is assumed. -/
theorem exists_hillFiniteGapDirichlet_quotient_laurent_bounds
    (n N : ℕ) (hn : 1≤n) (hnN : n≤N)
    (hclosed : ∀ (k : ℕ) (_hk : 1≤k), N<k → hillRealGapHalfLength q hq hr k=0) :
    ∃ R C₂ C₃ : ℝ, 0<R ∧ 0<C₂ ∧ 0<C₃ ∧ ∀ w : ℂ, R≤‖w‖ →
      hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) w≠0 →
      ‖w‖^3*‖hillAbelianSelectedGlobalPsi q hq hr n hn w/
        hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) w-
          hillDirichletResidueMoment q hq hr n hn N 0/w-
          hillDirichletResidueMoment q hq hr n hn N 1/w^2‖≤C₂ ∧
      ‖w‖^4*‖hillAbelianSelectedGlobalPsi q hq hr n hn w/
        hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) w-
          hillDirichletResidueMoment q hq hr n hn N 0/w-
          hillDirichletResidueMoment q hq hr n hn N 1/w^2-
          hillDirichletResidueMoment q hq hr n hn N 2/w^3‖≤C₃ := by
  obtain ⟨R₂,C₂,hR₂,hC₂,h₂⟩ := exists_hillDirichletPrincipalSum_laurent_two_bound q hq hr n hn N
  obtain ⟨R₃,C₃,hR₃,hC₃,h₃⟩ := exists_hillDirichletPrincipalSum_laurent_three_bound q hq hr n hn N
  refine ⟨max R₂ R₃,C₂,C₃,hR₂.trans_le (le_max_left _ _),hC₂,hC₃,?_⟩
  intro w hw hD
  rw [hillAbelianSelectedGlobalPsi_div_dirichlet_finite_gap q hq hr n N hn hnN hclosed w hD]
  exact ⟨h₂ w ((le_max_left _ _).trans hw) hD,h₃ w ((le_max_right _ _).trans hw) hD⟩

end NLS.KdV
