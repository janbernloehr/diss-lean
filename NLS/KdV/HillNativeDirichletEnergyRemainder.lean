import NLS.KdV.HillDirichletEnergyFourierBound
import NLS.SequenceSpaces.PositiveFourierInverseMajorant
import NLS.SequenceSpaces.BoundedCoordinateAnalytic

/-! # Native Hilbert quadratic remainder of the actual Dirichlet energies

The free energy and the actual mean are subtracted before taking the
positive sequence. The remaining nonlinear error has zero derivative at zero.
-/
noncomputable section
open Set Metric Complex Filter Topology Asymptotics NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

def hillNativeDirichletEnergyRemainder (u : Coeff 2) : Coeff 2 :=
  Coeff.positiveFamilySequence (fun k : ℕ+ =>
    hillScaledDirichletRoot h0q h0r (1/128) (k : ℕ) (Coeff.periodDouble u)-freeHillEnergy k-u 0+
      (u (-(k : ℤ))+u (k : ℤ))/2)

theorem exists_hillNativeDirichletEnergyRemainder_analytic_bound :
    ∃ η K : ℝ, 0 < η ∧ 0 < K ∧
      AnalyticOnNhd ℂ (hillNativeDirichletEnergyRemainder h0q h0r) (ball (0 : Coeff 2) η) ∧
      hillNativeDirichletEnergyRemainder h0q h0r 0 = 0 ∧
      HasFDerivAt (hillNativeDirichletEnergyRemainder h0q h0r) (0 : Coeff 2 →L[ℂ] Coeff 2) 0 ∧
      ∀ u ∈ ball (0 : Coeff 2) η,
        ‖hillNativeDirichletEnergyRemainder h0q h0r u‖ ≤ K*‖u‖^2 ∧
        (∀ k : ℕ+, hillNativeDirichletEnergyRemainder h0q h0r u (k : ℤ) =
          hillScaledDirichletRoot h0q h0r (1/128) (k : ℕ) (Coeff.periodDouble u)-freeHillEnergy k-u 0+
            (u (-(k : ℤ))+u (k : ℤ))/2) ∧
        ∀ j : ℤ, j ≤ 0 → hillNativeDirichletEnergyRemainder h0q h0r u j = 0 := by
  obtain ⟨ηt,hηt,hηt1,ht⟩ := exists_hillDirichlet_all_terminal_data h0q h0r
  obtain ⟨ηd,hηd,_,hd⟩ := exists_hillScaledDirichletRoot_all_analytic_chart h0q h0r (1/128) (by norm_num) (by norm_num)
  let η := min ηt (min ηd (1/(16*Real.exp 1)))
  have hη : 0 < η := lt_min hηt (lt_min hηd (by positivity))
  have hηt' : η ≤ ηt := min_le_left _ _
  have hηd' : η ≤ ηd := (min_le_right _ _).trans (min_le_left _ _)
  have hηs : η ≤ 1/(16*Real.exp 1) := (min_le_right _ _).trans (min_le_right _ _)
  have hsource (a : ℝ) (ha : η ≤ a) (u : Coeff 2) (hu : u ∈ ball 0 η) :
      Coeff.periodDouble u ∈ ball (0 : Coeff 2) a := by
    rw [mem_ball_zero_iff,Coeff.norm_periodDouble]
    exact (mem_ball_zero_iff.mp hu).trans_le ha
  let f := fun (u : Coeff 2) (k : ℕ+) =>
    hillScaledDirichletRoot h0q h0r (1/128) (k : ℕ) (Coeff.periodDouble u)-freeHillEnergy k-u 0+
      (u (-(k : ℤ))+u (k : ℤ))/2
  have hpoint (u : Coeff 2) (hu : u ∈ ball 0 η) (k : ℕ+) :
      ‖f u k‖ ≤ 1024*(Real.exp 1)^4*‖u‖^2/(k : ℝ) := by
    apply hillDirichletEnergy_moving_fourier_bound k u _ ((mem_ball_zero_iff.mp hu).le.trans hηs)
    · exact ((ht k).2.2 _ (hsource ηt hηt' u hu)).1.le
    · exact ((hd k).2 _ (hsource ηd hηd' u hu)).2.1
  have hmem (u : Coeff 2) (hu : u ∈ ball 0 η) := Coeff.positiveFamilySequence_bound (f u) (0 : Coeff 2) 1
    (1024*(Real.exp 1)^4*‖u‖^2) (by norm_num) (by positivity) (by
      intro k
      simpa only [lp.coeFn_zero,Pi.zero_apply,norm_zero,zero_add,one_mul] using hpoint u hu k)
  let R := hillNativeDirichletEnergyRemainder h0q h0r
  have hval (u : Coeff 2) (hu : u ∈ ball 0 η) (j : ℤ) :
      R u j = Coeff.positiveFamilyCoordinates (f u) j :=
    Coeff.ofFunctionOrZero_apply_of_mem 2 _ (hmem u hu).1 j
  let K := 2048*(Real.exp 1)^4
  have hK : 0 < K := by dsimp only [K]; positivity
  have hbound (u : Coeff 2) (hu : u ∈ ball 0 η) : ‖R u‖ ≤ K*‖u‖^2 := by
    apply (hmem u hu).2.trans_eq
    simp only [norm_zero,mul_zero,zero_add,one_mul,K]
    ring
  have hfa (k : ℕ+) : AnalyticOnNhd ℂ (fun u : Coeff 2 => f u k) (ball (0 : Coeff 2) η) := by
    intro u hu
    have hma := ((ht k).1 _ (hsource ηt hηt' u hu)).comp (Coeff.periodDouble.toContinuousLinearMap.analyticAt u)
    have hmean := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0).analyticAt u
    have hsum := ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (-(k : ℤ))).analyticAt u).add
      ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (k : ℤ)).analyticAt u)
    exact ((hma.sub analyticAt_const).sub hmean).add (hsum.div_const (c := 2))
  have hcoord (j : ℤ) : AnalyticOnNhd ℂ (fun u => R u j) (ball (0 : Coeff 2) η) := by
    intro u hu
    by_cases hj : 0 < j
    · apply (hfa (Coeff.positivePoleIndex j hj) u hu).congr
      filter_upwards [isOpen_ball.mem_nhds hu] with v hv
      rw [hval v hv j,Coeff.positiveFamilyCoordinates,dif_pos hj]
    · apply (analyticAt_const (v := (0 : ℂ))).congr
      filter_upwards [isOpen_ball.mem_nhds hu] with v hv
      rw [hval v hv j,Coeff.positiveFamilyCoordinates,dif_neg hj]
  have hRa := Coeff.analyticOnNhd_of_bounded_coordinatewise R isOpen_ball hcoord K (by
    intro u hu
    have hnu : ‖u‖ ≤ 1 := (mem_ball_zero_iff.mp hu).le.trans (hηt'.trans hηt1)
    apply (hbound u hu).trans
    calc
      _ ≤ K*1 := mul_le_mul_of_nonneg_left (by nlinarith [norm_nonneg u]) hK.le
      _ = _ := mul_one _)
  have hR0 : R 0 = 0 := by
    have h : ‖R 0‖ ≤ 0 := by simpa only [norm_zero,zero_pow (by norm_num : 2 ≠ 0),mul_zero] using hbound 0 (mem_ball_self hη)
    exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
  have hDR : HasFDerivAt R (0 : Coeff 2 →L[ℂ] Coeff 2) 0 := by
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    have ho : (fun h : Coeff 2 => R (0+h)-R 0-(0 : Coeff 2 →L[ℂ] Coeff 2) h)
        =O[𝓝 0] (fun h => ‖h‖^2) := by
      apply Asymptotics.IsBigO.of_bound K
      filter_upwards [ball_mem_nhds (0 : Coeff 2) hη] with u hu
      simpa only [zero_add,hR0,zero_apply,sub_zero,Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg ‖u‖)] using hbound u hu
    exact ho.trans_isLittleO (isLittleO_norm_pow_id (by norm_num : 1 < (2 : ℕ)))
  refine ⟨η,K,hη,hK,hRa,hR0,hDR,?_⟩
  intro u hu
  refine ⟨hbound u hu,?_,?_⟩
  · intro k
    rw [hval u hu,Coeff.positiveFamilyCoordinates_nat]
  · intro j hj
    rw [hval u hu,Coeff.positiveFamilyCoordinates,dif_neg (by omega : ¬ 0 < j)]

end NLS.KdV
