import NLS.KdV.HillGapMidpointQuadraticBound
import NLS.KdV.HillAllMidpointAnalytic
import NLS.SequenceSpaces.PositiveFourierInverseMajorant
import NLS.SequenceSpaces.BoundedCoordinateAnalytic

/-! # Native Hilbert quadratic remainder of the actual symmetric gap midpoints

The free energy and the actual mean are subtracted before taking the
positive sequence. The remaining nonlinear error has zero derivative at zero.
-/
noncomputable section
open Set Metric Complex Filter Topology Asymptotics NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

def hillNativeGapMidpointRemainder (u : Coeff 2) : Coeff 2 :=
  Coeff.positiveFamilySequence (fun k : ℕ+ =>
    hillLocalGapMidpoint 0 h0q h0r (k : ℕ) (Coeff.periodDouble u)-freeHillEnergy k-u 0)

theorem exists_hillNativeGapMidpointRemainder_analytic_bound :
    ∃ η K : ℝ, 0 < η ∧ 0 < K ∧
      AnalyticOnNhd ℂ (hillNativeGapMidpointRemainder h0q h0r) (ball (0 : Coeff 2) η) ∧
      hillNativeGapMidpointRemainder h0q h0r 0 = 0 ∧
      HasFDerivAt (hillNativeGapMidpointRemainder h0q h0r) (0 : Coeff 2 →L[ℂ] Coeff 2) 0 ∧
      ∀ u ∈ ball (0 : Coeff 2) η,
        ‖hillNativeGapMidpointRemainder h0q h0r u‖ ≤ K*‖u‖^2 ∧
        (∀ k : ℕ+, hillNativeGapMidpointRemainder h0q h0r u (k : ℤ) =
          hillLocalGapMidpoint 0 h0q h0r (k : ℕ) (Coeff.periodDouble u)-freeHillEnergy k-u 0) ∧
        ∀ j : ℤ, j ≤ 0 → hillNativeGapMidpointRemainder h0q h0r u j = 0 := by
  obtain ⟨ηb,C,hηb,hηb1,hC,hpoint0⟩ := exists_hillLocalGapMidpoint_all_quadratic_bound h0q h0r
  obtain ⟨ηa,hηa,ha⟩ := exists_hillLocalGapMidpoint_all_periodOne_analytic h0q h0r
  let η := min ηb ηa
  have hη : 0 < η := lt_min hηb hηa
  have hηb' : η ≤ ηb := min_le_left _ _
  have hηa' : η ≤ ηa := min_le_right _ _
  let f := fun (u : Coeff 2) (k : ℕ+) =>
    hillLocalGapMidpoint 0 h0q h0r (k : ℕ) (Coeff.periodDouble u)-freeHillEnergy k-u 0
  have hpoint (u : Coeff 2) (hu : u ∈ ball 0 η) (k : ℕ+) :
      ‖f u k‖ ≤ C*‖u‖^2/(k : ℝ) := hpoint0 u (ball_subset_ball hηb' hu) k
  have hmem (u : Coeff 2) (hu : u ∈ ball 0 η) := Coeff.positiveFamilySequence_bound (f u) (0 : Coeff 2) 1
    (C*‖u‖^2) (by norm_num) (by positivity) (by
      intro k
      simpa only [lp.coeFn_zero,Pi.zero_apply,norm_zero,zero_add,one_mul] using hpoint u hu k)
  let R := hillNativeGapMidpointRemainder h0q h0r
  have hval (u : Coeff 2) (hu : u ∈ ball 0 η) (j : ℤ) :
      R u j = Coeff.positiveFamilyCoordinates (f u) j :=
    Coeff.ofFunctionOrZero_apply_of_mem 2 _ (hmem u hu).1 j
  let K := 2*C
  have hK : 0 < K := by dsimp only [K]; positivity
  have hbound (u : Coeff 2) (hu : u ∈ ball 0 η) : ‖R u‖ ≤ K*‖u‖^2 := by
    apply (hmem u hu).2.trans_eq
    simp only [norm_zero,mul_zero,zero_add,one_mul,K]
    ring
  have hfa (k : ℕ+) : AnalyticOnNhd ℂ (fun u : Coeff 2 => f u k) (ball (0 : Coeff 2) η) := by
    intro u hu
    have hma := ha k u (ball_subset_ball hηa' hu)
    have hmean := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0).analyticAt u
    exact (hma.sub analyticAt_const).sub hmean
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
    have hnu : ‖u‖ ≤ 1 := (mem_ball_zero_iff.mp hu).le.trans (hηb'.trans hηb1)
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
