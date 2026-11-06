import NLS.KdV.HillNativeAmplitudePhysical
import NLS.KdV.HillNativeDirichletMidpointCoordinates
import NLS.KdV.HillNativeDirichletTerminalSequence
import NLS.KdV.HillAbelianCoordinateSequence
import NLS.SequenceSpaces.PositiveAnalyticWeightedProduct

/-! # Native positive Abelian coordinates in the actual weighted half-shift target -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillAbelianTargetWeight_one_sqrt (j : ℤ) :
    hillAbelianTargetWeight SpectralWeight.one j = Real.sqrt (1+|(j : ℝ)|) := by
  simp only [hillAbelianTargetWeight,Weight.product_apply,SpectralWeight.doubleIndex_apply,
    SpectralWeight.one_apply,one_mul,Weight.sobolev_apply,Real.sqrt_eq_rpow]

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

def hillNativePositiveAbelianCoordinates (Φ : Coeff 2 → Coeff 2) (u : Coeff 2) :
    WeightedCoeff (hillAbelianTargetWeight SpectralWeight.one) 2 :=
  Coeff.positiveWeightedProduct (hillAbelianTargetWeight SpectralWeight.one)
    (fun v k => hillNativeAbelianAmplitudePrefactor h0q h0r k v*exp (I*Φ v (k : ℤ)))
    (fun v => hillNativeDirichletGapTerminals h0q h0r v-hillNativeDirichletMidpointDisplacements h0q h0r v) u

theorem exists_hillNativePositiveAbelianCoordinates_analytic_bound
    (Φ : Coeff 2 → Coeff 2) (ε M : ℝ) (hε : 0 < ε)
    (hΦ : AnalyticOnNhd ℂ Φ (ball (0 : Coeff 2) ε))
    (hΦb : ∀ u ∈ ball (0 : Coeff 2) ε, ‖Φ u‖ ≤ M) :
    ∃ η K : ℝ, 0 < η ∧ η ≤ ε ∧ 0 < K ∧
      AnalyticOnNhd ℂ (hillNativePositiveAbelianCoordinates h0q h0r Φ) (ball (0 : Coeff 2) η) ∧
      hillNativePositiveAbelianCoordinates h0q h0r Φ 0 = 0 ∧
      ∀ u ∈ ball (0 : Coeff 2) η,
        ‖hillNativePositiveAbelianCoordinates h0q h0r Φ u‖ ≤ K*(‖u‖+‖u‖^2) ∧
        (∀ k : ℕ+, (hillNativePositiveAbelianCoordinates h0q h0r Φ u).val (k : ℤ) =
          hillNativeAbelianAmplitudePrefactor h0q h0r k u*
            (hillScaledComplexDirichletGapTerminal h0q h0r (1/128) (k : ℕ) (Coeff.periodDouble u)-
              (hillScaledDirichletRoot h0q h0r (1/128) (k : ℕ) (Coeff.periodDouble u)-
                hillLocalGapMidpoint 0 h0q h0r (k : ℕ) (Coeff.periodDouble u)))*exp (I*Φ u (k : ℤ))) ∧
        ∀ j : ℤ, j ≤ 0 → (hillNativePositiveAbelianCoordinates h0q h0r Φ u).val j = 0 := by
  obtain ⟨ηx,Kx,hηx,hKx,hXa,hX⟩ := exists_hillNativeDirichletGapTerminals_analytic_bound h0q h0r
  obtain ⟨ηa,Ka,hηa,hKa,hAa,hA0,_,hA⟩ := exists_hillNativeDirichletMidpointDisplacements_analytic_bound h0q h0r
  obtain ⟨ηm,C,hηm,hC,hm⟩ := exists_hillNativeAbelianAmplitudePrefactor_all_analytic_bound h0q h0r
  let η := min ηx (min ηa (min ηm (min ε 1)))
  have hη : 0 < η := lt_min hηx (lt_min hηa (lt_min hηm (lt_min hε (by norm_num))))
  have hηx' : η ≤ ηx := min_le_left _ _
  have hηa' : η ≤ ηa := (min_le_right _ _).trans (min_le_left _ _)
  have hηm' : η ≤ ηm := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηε : η ≤ ε := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hη1 : η ≤ 1 := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let F := fun u => hillNativeDirichletGapTerminals h0q h0r u-hillNativeDirichletMidpointDisplacements h0q h0r u
  let m := fun (u : Coeff 2) (k : ℕ+) => hillNativeAbelianAmplitudePrefactor h0q h0r k u*exp (I*Φ u (k : ℤ))
  let D := Kx+1+Ka
  have hD : 0 < D := by dsimp only [D]; positivity
  have hFa : AnalyticOnNhd ℂ F (ball (0 : Coeff 2) η) :=
    (hXa.mono (ball_subset_ball hηx')).sub (hAa.mono (ball_subset_ball hηa'))
  have hFb (u : Coeff 2) (hu : u ∈ ball 0 η) : ‖F u‖ ≤ D*(‖u‖+‖u‖^2) := by
    apply (norm_sub_le _ _).trans
    apply (add_le_add (hX u (ball_subset_ball hηx' hu)).1 (hA u (ball_subset_ball hηa' hu)).1).trans
    dsimp only [D]
    nlinarith [mul_nonneg hKa.le (norm_nonneg u)]
  have hFN (u : Coeff 2) (hu : u ∈ ball 0 η) : ‖F u‖ ≤ 2*D := by
    have hnu : ‖u‖ ≤ 1 := (mem_ball_zero_iff.mp hu).le.trans hη1
    have h := hFb u hu
    have hh := mul_le_mul_of_nonneg_left (show ‖u‖+‖u‖^2 ≤ 2 by nlinarith [norm_nonneg u]) hD.le
    linarith
  have hma (k : ℕ+) : AnalyticOnNhd ℂ (fun u => m u k) (ball (0 : Coeff 2) η) := by
    intro u hu
    have hz := ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (k : ℤ)).analyticAt (Φ u)).comp
      (hΦ u (ball_subset_ball hηε hu))
    exact ((hm k).1 u (ball_subset_ball hηm' hu)).mul
      ((analyticAt_const.mul hz).cexp)
  have hmb (u : Coeff 2) (hu : u ∈ ball 0 η) (k : ℕ+) :
      hillAbelianTargetWeight SpectralWeight.one (k : ℤ)*‖m u k‖ ≤ C*Real.exp M := by
    have hz : ‖Φ u (k : ℤ)‖ ≤ M := (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) (Φ u) _).trans
      (hΦb u (ball_subset_ball hηε hu))
    have he : ‖exp (I*Φ u (k : ℤ))‖ ≤ Real.exp M := by
      apply (Complex.norm_exp_le_exp_norm _).trans
      rw [norm_mul,norm_I,one_mul]
      exact Real.exp_le_exp.mpr hz
    rw [hillAbelianTargetWeight_one_sqrt,show ((k : ℤ) : ℝ) = (k : ℝ) by norm_cast,
      abs_of_pos (by positivity : (0 : ℝ) < k)]
    change Real.sqrt (1+(k : ℝ))*‖hillNativeAbelianAmplitudePrefactor h0q h0r k u*exp (I*Φ u (k : ℤ))‖ ≤ _
    rw [norm_mul,← mul_assoc]
    exact mul_le_mul ((hm k).2 u (ball_subset_ball hηm' hu)) he (norm_nonneg _) hC.le
  have hproduct := Coeff.positiveWeightedProduct_analytic_bound
    (hillAbelianTargetWeight SpectralWeight.one) m F isOpen_ball hFa hma (C*Real.exp M) (2*D)
    (by positivity) hmb hFN
  let Y := hillNativePositiveAbelianCoordinates h0q h0r Φ
  have hY (u : Coeff 2) (hu : u ∈ ball 0 η) := hproduct.2 u hu
  have hX0 : hillNativeDirichletGapTerminals h0q h0r 0 = 0 := by
    have h : ‖hillNativeDirichletGapTerminals h0q h0r 0‖ ≤ 0 := by
      simpa only [norm_zero,zero_pow (by norm_num : 2 ≠ 0),zero_add,mul_zero] using (hX 0 (mem_ball_self hηx)).1
    exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
  have hF0 : F 0 = 0 := by dsimp only [F]; rw [hX0,hA0,sub_self]
  have hY0 : Y 0 = 0 := by
    have h := (hY 0 (mem_ball_self hη)).1
    rw [hF0,norm_zero,mul_zero] at h
    exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
  refine ⟨η,2*(C*Real.exp M)*D,hη,hηε,by positivity,hproduct.1,hY0,?_⟩
  intro u hu
  refine ⟨?_,?_,(hY u hu).2.2⟩
  · exact ((hY u hu).1.trans (mul_le_mul_of_nonneg_left (hFb u hu) (by positivity))).trans_eq (by ring)
  · intro k
    have h := (hY u hu).2.1 k
    dsimp only [m,F] at h
    rw [lp.coeFn_sub,Pi.sub_apply,(hX u (ball_subset_ball hηx' hu)).2.1 k,
      (hA u (ball_subset_ball hηa' hu)).2.2.1 k] at h
    exact h.trans (by ring)

end NLS.KdV
