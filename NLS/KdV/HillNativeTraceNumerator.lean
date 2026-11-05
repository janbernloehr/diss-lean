import NLS.KdV.HillL2EnergyDiscTraceBounds
import NLS.KdV.HillNativeFilledRootInverseBound
import NLS.ComplexAnalysis.AnalyticDiscDerivativeBounds

/-! # Uniform analytic filled trace numerators and their energy derivatives -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

def hillNativeFilledTraceNumerator (k : ℕ+) (t : ℂ × Coeff 2) : ℂ :=
  deriv (hillL2Discriminant (Coeff.periodDouble t.2)) t.1 /
    hillFilledFreeGapRoot h0q h0r (k : ℕ) (t.1,Coeff.periodDouble t.2)

theorem exists_hillNativeFilledTraceNumerator_all_bound :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧ ∀ k : ℕ+,
      AnalyticOnNhd ℂ (hillNativeFilledTraceNumerator h0q h0r k)
        (closedBall (freeHillEnergy k) (k : ℝ) ×ˢ ball (0 : Coeff 2) η) ∧
      ∀ u ∈ ball (0 : Coeff 2) η,
        (∀ E ∈ closedBall (freeHillEnergy k) (k : ℝ),
          ‖hillNativeFilledTraceNumerator h0q h0r k (E,u)‖ ≤ C) ∧
        ∀ E ∈ closedBall (freeHillEnergy k) ((k : ℝ)/2),
          ‖deriv (fun w => hillNativeFilledTraceNumerator h0q h0r k (w,u)) E‖ ≤ 2*C/(k : ℝ) := by
  obtain ⟨ηu,hηu,_,hU⟩ := exists_hillFilledFreeGapRoot_all_radius_data h0q h0r
  obtain ⟨ηi,C,hηi,hC,hI⟩ := exists_hillFilledFreeGapRoot_all_inverse_bound h0q h0r
  let η := min ηu (min ηi (min 1 (1/(4*Real.exp 1))))
  have hη : 0 < η := lt_min hηu (lt_min hηi (lt_min (by norm_num) (by positivity)))
  have hηu' : η ≤ ηu := min_le_left _ _
  have hηi' : η ≤ ηi := (min_le_right _ _).trans (min_le_left _ _)
  have hη1 : η ≤ 1 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηs : η ≤ 1/(4*Real.exp 1) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let M := (2*Real.exp 1+8*(Real.exp 1)^2)^2+9
  have hM : 0 < M := by dsimp only [M]; positivity
  have hsource (u : Coeff 2) (hu : u ∈ ball 0 η) : Coeff.periodDouble u ∈ ball (0 : Coeff 2) ηu := by
    rw [mem_ball_zero_iff,Coeff.norm_periodDouble]
    exact (mem_ball_zero_iff.mp hu).trans_le hηu'
  have hD := analyticOnNhd_spectral_deriv_of_analyticOnNhd
    (fun t : ℂ × Coeff 2 => hillL2Discriminant t.2 t.1) univ isOpen_univ
    analyticOnNhd_hillL2Discriminant_joint
  refine ⟨η,M*C,hη,mul_pos hM hC,?_⟩
  intro k
  let T := hillNativeFilledTraceNumerator h0q h0r k
  have hTa : AnalyticOnNhd ℂ T (closedBall (freeHillEnergy k) (k : ℝ) ×ˢ ball (0 : Coeff 2) η) := by
    intro t ht
    have hp := analyticAt_fst.prod ((Coeff.periodDouble.toContinuousLinearMap.analyticAt t.2).comp analyticAt_snd)
    exact ((hD (t.1,Coeff.periodDouble t.2) (mem_univ _)).comp (f := fun s : ℂ × Coeff 2 => (s.1,Coeff.periodDouble s.2)) hp).div
      (((hU k).1 (t.1,Coeff.periodDouble t.2) ⟨ht.1,hsource t.2 ht.2⟩).comp (f := fun s : ℂ × Coeff 2 => (s.1,Coeff.periodDouble s.2)) hp)
      (((hU k).2 _ (hsource t.2 ht.2) t.1 ht.1).1)
  refine ⟨hTa,?_⟩
  intro u hu
  have hnu : ‖u‖ ≤ 1 := (mem_ball_zero_iff.mp hu).le.trans hη1
  have hs : 4*Real.exp 1*‖u‖ ≤ 1 := by
    have h := (le_div_iff₀ (by positivity : 0 < 4*Real.exp 1)).mp ((mem_ball_zero_iff.mp hu).le.trans hηs)
    nlinarith
  have hk : (0 : ℝ) < k := by positivity
  have hb (E : ℂ) (hE : E ∈ closedBall (freeHillEnergy k) (k : ℝ)) : ‖T (E,u)‖ ≤ M*C := by
    have hd := hillL2Discriminant_freeEnergy_derivative_bound u hnu hs k E hE
    have hi := (hI k u (ball_subset_ball hηi' hu)).2 E hE
    change ‖deriv (hillL2Discriminant (Coeff.periodDouble u)) E /
      hillFilledFreeGapRoot h0q h0r (k : ℕ) (E,Coeff.periodDouble u)‖ ≤ _
    rw [div_eq_mul_inv,norm_mul]
    apply (mul_le_mul hd hi (norm_nonneg _) (by positivity)).trans_eq
    change (M/(k : ℝ))*(C*(k : ℝ)) = M*C
    field_simp
  refine ⟨hb,?_⟩
  have ha : AnalyticOnNhd ℂ (fun E => T (E,u)) (closedBall (freeHillEnergy k) (k : ℝ)) := by
    intro E hE
    exact (hTa (E,u) ⟨hE,hu⟩).comp (f := fun E : ℂ => (E,u)) (analyticAt_id.prod analyticAt_const)
  intro E hE
  have h := norm_deriv_le_of_analytic_closedDisc_bound (freeHillEnergy k) ha
    (by linarith : (k : ℝ)/2 < k) (M*C) hb hE
  apply h.trans_eq
  field_simp
  ring

end NLS.KdV
