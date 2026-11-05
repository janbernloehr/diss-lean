import NLS.KdV.HillDirichletSheetFourierBound
import NLS.KdV.HillNativeFilledRootInverseBound
import NLS.SequenceSpaces.PositiveFourierInverseMajorant
import NLS.SequenceSpaces.BoundedCoordinateAnalytic

/-! # The actual unscaled Dirichlet terminal sequence is natively Hilbert analytic

The complex Fourier leading term, inverse-index quadratic remainder and
filled-root inverse bound give one actual ell2 sequence before all gaps.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

def hillNativeDirichletGapTerminals (u : Coeff 2) : Coeff 2 :=
  Coeff.positiveFamilySequence (fun k : ℕ+ =>
    hillScaledComplexDirichletGapTerminal h0q h0r (1/128) (k : ℕ) (Coeff.periodDouble u))

theorem exists_hillNativeDirichletGapTerminals_analytic_bound :
    ∃ η K : ℝ, 0 < η ∧ 0 < K ∧
      AnalyticOnNhd ℂ (hillNativeDirichletGapTerminals h0q h0r) (ball (0 : Coeff 2) η) ∧
      ∀ u ∈ ball (0 : Coeff 2) η,
        ‖hillNativeDirichletGapTerminals h0q h0r u‖ ≤ K*(‖u‖+‖u‖^2) ∧
        (∀ k : ℕ+, hillNativeDirichletGapTerminals h0q h0r u (k : ℤ) =
          hillScaledComplexDirichletGapTerminal h0q h0r (1/128) (k : ℕ) (Coeff.periodDouble u)) ∧
        ∀ j : ℤ, j ≤ 0 → hillNativeDirichletGapTerminals h0q h0r u j = 0 := by
  obtain ⟨ηt,hηt,_,ht⟩ := exists_hillDirichlet_all_terminal_data h0q h0r
  obtain ⟨ηd,hηd,_,hd⟩ := exists_hillScaledDirichletRoot_all_analytic_chart h0q h0r (1/128) (by norm_num) (by norm_num)
  obtain ⟨ηr,C,hηr,hC,hroot⟩ := exists_hillFilledFreeGapRoot_all_inverse_bound h0q h0r
  let σ := min ηt ηd
  let ρ := min ηr (min 1 (1/(16*Real.exp 1)))
  let η := min σ ρ
  have hη : 0 < η := lt_min (lt_min hηt hηd) (lt_min hηr (lt_min zero_lt_one (by positivity)))
  have hηt' : η ≤ ηt := (min_le_left _ _).trans (min_le_left _ _)
  have hηd' : η ≤ ηd := (min_le_left _ _).trans (min_le_right _ _)
  have hηr' : η ≤ ηr := (min_le_right _ _).trans (min_le_left _ _)
  have hη1 : η ≤ 1 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηs : η ≤ 1/(16*Real.exp 1) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hsource (a : ℝ) (ha : η ≤ a) (u : Coeff 2) (hu : u ∈ ball 0 η) :
      Coeff.periodDouble u ∈ ball (0 : Coeff 2) a := by
    rw [mem_ball_zero_iff,Coeff.norm_periodDouble]
    exact (mem_ball_zero_iff.mp hu).trans_le ha
  let X := fun (u : Coeff 2) (k : ℕ+) =>
    hillScaledComplexDirichletGapTerminal h0q h0r (1/128) (k : ℕ) (Coeff.periodDouble u)
  have hpoint (u : Coeff 2) (hu : u ∈ ball 0 η) (k : ℕ+) :
      ‖X u k‖ ≤ C*(‖u (k : ℤ)‖+‖u (-(k : ℤ))‖+32*(Real.exp 1)^3*‖u‖^2/(k : ℝ)) := by
    let μ := hillScaledDirichletRoot h0q h0r (1/128) (k : ℕ) (Coeff.periodDouble u)
    have ht' := (ht k).2.2 _ (hsource ηt hηt' u hu)
    have hE : ‖μ-freeHillEnergy k‖ ≤ (k : ℝ)/16 := ht'.1.le
    have hz : hillL2DirichletCharacteristic (Coeff.periodDouble u) μ = 0 :=
      ((hd k).2 _ (hsource ηd hηd' u hu)).2.1
    have hs := hillDirichletSheetRoot_moving_fourier_bound k u μ ((mem_ball_zero_iff.mp hu).le.trans hηs) hE hz
    have hμ : μ ∈ closedBall (freeHillEnergy k) (k : ℝ) := by
      rw [mem_closedBall_iff_norm]
      exact hE.trans (by linarith [show (0 : ℝ) < k by positivity])
    have hUi := (hroot k u (ball_subset_ball hηr' hu)).2 μ hμ
    calc
      _ = ‖hillDirichletSheetRoot (Coeff.periodDouble u) μ‖*
          ‖(hillFilledFreeGapRoot h0q h0r (k : ℕ) (μ,Coeff.periodDouble u))⁻¹‖ := by
        dsimp only [X]
        rw [hillScaledComplexDirichletGapTerminal,norm_div,norm_inv,div_eq_mul_inv]
      _ ≤ ‖hillDirichletSheetRoot (Coeff.periodDouble u) μ‖*(C*(k : ℝ)) :=
        mul_le_mul_of_nonneg_left hUi (norm_nonneg _)
      _ = C*((k : ℝ)*‖hillDirichletSheetRoot (Coeff.periodDouble u) μ‖) := by ring
      _ ≤ C*((‖u (-(k : ℤ))‖+‖u (k : ℤ)‖)/2+32*(Real.exp 1)^3*‖u‖^2/(k : ℝ)) :=
        mul_le_mul_of_nonneg_left hs hC.le
      _ ≤ _ := by gcongr; nlinarith [norm_nonneg (u (k : ℤ)),norm_nonneg (u (-(k : ℤ)))]
  have hmem (u : Coeff 2) (hu : u ∈ ball 0 η) := Coeff.positiveFamilySequence_bound (X u) u C
    (32*(Real.exp 1)^3*‖u‖^2) hC.le (by positivity) (hpoint u hu)
  let F := hillNativeDirichletGapTerminals h0q h0r
  have hval (u : Coeff 2) (hu : u ∈ ball 0 η) (j : ℤ) :
      F u j = Coeff.positiveFamilyCoordinates (X u) j :=
    Coeff.ofFunctionOrZero_apply_of_mem 2 _ (hmem u hu).1 j
  let K := C*(2+64*(Real.exp 1)^3)
  have hK : 0 < K := by dsimp only [K]; positivity
  have hbound (u : Coeff 2) (hu : u ∈ ball 0 η) : ‖F u‖ ≤ K*(‖u‖+‖u‖^2) := by
    apply (hmem u hu).2.trans
    dsimp only [K]
    conv_rhs => rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hC.le
    nlinarith [mul_nonneg (by positivity : 0 ≤ 64*(Real.exp 1)^3) (norm_nonneg u)]
  have hcoord (j : ℤ) : AnalyticOnNhd ℂ (fun u => F u j) (ball (0 : Coeff 2) η) := by
    intro u hu
    by_cases hj : 0 < j
    · have ha : AnalyticAt ℂ (fun v : Coeff 2 => X v (Coeff.positivePoleIndex j hj)) u :=
        ((ht (Coeff.positivePoleIndex j hj)).2.1 _ (hsource ηt hηt' u hu)).comp
          (Coeff.periodDouble.toContinuousLinearMap.analyticAt u)
      apply ha.congr
      filter_upwards [isOpen_ball.mem_nhds hu] with v hv
      rw [hval v hv j,Coeff.positiveFamilyCoordinates,dif_pos hj]
    · apply (analyticAt_const (v := (0 : ℂ))).congr
      filter_upwards [isOpen_ball.mem_nhds hu] with v hv
      rw [hval v hv j,Coeff.positiveFamilyCoordinates,dif_neg hj]
  have ha := Coeff.analyticOnNhd_of_bounded_coordinatewise F isOpen_ball hcoord (2*K) (by
    intro u hu
    have hnu : ‖u‖ ≤ 1 := (mem_ball_zero_iff.mp hu).le.trans hη1
    apply (hbound u hu).trans
    calc
      _ ≤ K*2 := mul_le_mul_of_nonneg_left (by nlinarith [norm_nonneg u]) hK.le
      _ = _ := by ring)
  refine ⟨η,K,hη,hK,ha,?_⟩
  intro u hu
  refine ⟨hbound u hu,?_,?_⟩
  · intro k
    rw [hval u hu,Coeff.positiveFamilyCoordinates_nat]
  · intro j hj
    rw [hval u hu,Coeff.positiveFamilyCoordinates,dif_neg (by omega : ¬ 0 < j)]

end NLS.KdV
