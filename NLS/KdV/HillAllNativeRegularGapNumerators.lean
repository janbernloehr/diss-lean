import NLS.KdV.HillAllRadiusRootProduct
import NLS.KdV.HillNativeRegularGapNumerator
import NLS.ComplexAnalysis.NativeOwnPeriodSubtraction
/-! # Native regular gap numerators including the finite head

The actual normalized family and filled root give one jointly analytic,
uniformly bounded output Hilbert numerator on every filled energy disc.
The complete genuine Bochner period is zero, including the own mode.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillNative_all_regular_gap_numerators :
    ∃ ε : ℝ, 0 < ε ∧ ∀ η : ℝ, 0 < η → η ≤ ε →
      ∀ G : ℂ × Coeff 2 → Coeff 2,
      AnalyticOnNhd ℂ G (univ ×ˢ ball (0 : Coeff 2) η) →
      ∀ C : ℝ, 0 ≤ C →
      (∀ u ∈ ball (0 : Coeff 2) η, ∀ k : ℕ+,
        (∀ E ∈ sphere (freeHillEnergy k) (k : ℝ),
          (E,periodOneL2Inclusion u) ∈ hillHminusContinuationDomain ∧
          ‖(hillHminusContinuedRoot (E,periodOneL2Inclusion u))⁻¹ • G (E,u)‖ ≤ C/(k : ℝ)) ∧
        CircleIntegrable (fun E : ℂ => (hillHminusContinuedRoot (E,periodOneL2Inclusion u))⁻¹ • G (E,u)) (freeHillEnergy k) (k : ℝ) ∧
        (2*(Real.pi : ℂ))⁻¹ • (∮ E in C(freeHillEnergy k,(k : ℝ)),
          (hillHminusContinuedRoot (E,periodOneL2Inclusion u))⁻¹ • G (E,u)) = lp.single 2 (k : ℤ) 1) →
      ∃ M : ℝ, 0 < M ∧ ∀ k : ℕ+,
        AnalyticOnNhd ℂ (hillNativeRegularGapNumerator h0q h0r G k)
          (closedBall (freeHillEnergy k) (k : ℝ) ×ˢ ball (0 : Coeff 2) η) ∧
        ∀ u ∈ ball (0 : Coeff 2) η,
          (∀ E ∈ closedBall (freeHillEnergy k) (k : ℝ), ‖hillNativeRegularGapNumerator h0q h0r G k (E,u)‖ ≤ M) ∧
          CircleIntegrable (fun E : ℂ => (hillFreeGapQuadraticRoot h0q h0r (k : ℕ) (E,Coeff.periodDouble u))⁻¹ •
            hillNativeRegularGapNumerator h0q h0r G k (E,u)) (freeHillEnergy k) (k : ℝ) ∧
          (∮ E in C(freeHillEnergy k,(k : ℝ)), (hillFreeGapQuadraticRoot h0q h0r (k : ℕ) (E,Coeff.periodDouble u))⁻¹ •
            hillNativeRegularGapNumerator h0q h0r G k (E,u)) = 0 := by
  obtain ⟨εR,hεR,hproduct⟩ := exists_hillRadiusEnergyCircle_all_root_product_matching h0q h0r
  obtain ⟨εQ,hεQ,_,hQ⟩ := exists_hillRadiusEnergyCircle_all_quadratic_data h0q h0r
  obtain ⟨εU,hεU,_,hU⟩ := exists_hillFilledFreeGapRoot_all_radius_data h0q h0r
  refine ⟨min εR (min εQ εU),lt_min hεR (lt_min hεQ hεU),?_⟩
  intro η hη hηsmall G hGa C hC hdata
  have hsourceQ (u : Coeff 2) (hu : u ∈ ball 0 η) : Coeff.periodDouble u ∈ ball (0 : Coeff 2) εQ := by
    rw [mem_ball_zero_iff,Coeff.norm_periodDouble]
    exact (mem_ball_zero_iff.mp hu).trans_le (hηsmall.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hsourceU (u : Coeff 2) (hu : u ∈ ball 0 η) : Coeff.periodDouble u ∈ ball (0 : Coeff 2) εU := by
    rw [mem_ball_zero_iff,Coeff.norm_periodDouble]
    exact (mem_ball_zero_iff.mp hu).trans_le (hηsmall.trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hmatch := hproduct η hη (hηsmall.trans (min_le_left _ _))
    (fun u hu k E hE => ((hdata u hu k).1 E hE).1)
  refine ⟨2*C+1,by positivity,?_⟩
  intro k
  let f := fun t : ℂ × Coeff 2 => (-I/hillFilledFreeGapRoot h0q h0r (k : ℕ) (t.1,Coeff.periodDouble t.2)) • G t
  have hf : AnalyticOnNhd ℂ f (closedBall (freeHillEnergy k) (k : ℝ) ×ˢ ball (0 : Coeff 2) η) := by
    intro t ht
    have hUt := (hU k).1 (t.1,Coeff.periodDouble t.2) ⟨ht.1,hsourceU t.2 ht.2⟩
    have hUa := hUt.comp (f := fun s : ℂ × Coeff 2 => (s.1,Coeff.periodDouble s.2))
      (analyticAt_fst.prod ((Coeff.periodDouble.toContinuousLinearMap.analyticAt t.2).comp analyticAt_snd))
    have hUn := ((hU k).2 _ (hsourceU t.2 ht.2) t.1 ht.1).1
    exact (analyticAt_const.div hUa hUn).smul (hGa t ⟨mem_univ _,ht.2⟩)
  refine ⟨?_,?_⟩
  · intro t ht
    exact (hf t ht).sub analyticAt_const
  · intro u hu
    let Q := fun E : ℂ => hillFreeGapQuadraticRoot h0q h0r (k : ℕ) (E,Coeff.periodDouble u)
    let U := fun E : ℂ => hillFilledFreeGapRoot h0q h0r (k : ℕ) (E,Coeff.periodDouble u)
    let S := fun E : ℂ => hillHminusContinuedRoot (E,periodOneL2Inclusion u)
    let e : Coeff 2 := lp.single 2 (k : ℤ) 1
    have hp := hsourceQ u hu
    have hprod (E : ℂ) (hE : E ∈ sphere (freeHillEnergy k) (k : ℝ)) : Q E*U E=S E :=
      hmatch k u hu E hE
    have hdist (E : ℂ) (hE : E ∈ sphere (freeHillEnergy k) (k : ℝ)) : (k : ℝ)/2 ≤ ‖E-freeHillEnergy k‖ := by
      rw [mem_sphere_iff_norm.mp hE]
      nlinarith [show (0 : ℝ) ≤ k by positivity]
    have hfslice : AnalyticOnNhd ℂ (fun E => (-I/U E) • G (E,u)) (closedBall (freeHillEnergy k) (k : ℝ)) := by
      intro E hE
      exact (hf (E,u) ⟨hE,hu⟩).comp (f := fun E : ℂ => (E,u)) (analyticAt_id.prod analyticAt_const)
    have hbound := norm_native_own_regular_numerator_le (fun E => G (E,u)) Q U S e (freeHillEnergy k) (k : ℝ) C
      (by positivity) hfslice hprod
      (fun E hE => ((hQ k).2.1 _ hp E (hdist E hE)).2.1)
      (fun E hE => by simpa only [mem_sphere_iff_norm.mp hE] using ((hQ k).2.1 _ hp E (hdist E hE)).2.2.2)
      (fun E hE => ((hdata u hu k).1 E hE).2)
    have hπ : (2*(Real.pi : ℂ)) ≠ 0 := mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)
    have hraw : (∮ E in C(freeHillEnergy k,(k : ℝ)), (S E)⁻¹ • G (E,u)) = (2*(Real.pi : ℂ)) • e := by
      have hh := congrArg (fun v : Coeff 2 => (2*(Real.pi : ℂ)) • v) (hdata u hu k).2.2
      simpa only [smul_smul,mul_inv_cancel₀ hπ,one_smul] using hh
    have hperiod := native_own_period_subtraction (fun E => G (E,u)) Q U S e (freeHillEnergy k) (k : ℝ)
      (by positivity) hprod (hdata u hu k).2.1 ((hQ k).2.2 _ hp).1 hraw ((hQ k).2.2 _ hp).2
    refine ⟨?_,hperiod⟩
    intro E hE
    change ‖(-I/U E) • G (E,u)-e‖ ≤ 2*C+1
    have he : ‖e‖ = 1 := by simp only [e,lp.norm_single (by norm_num : 0 < (2 : ENNReal)),norm_one]
    simpa only [he] using hbound E hE
end NLS.KdV
