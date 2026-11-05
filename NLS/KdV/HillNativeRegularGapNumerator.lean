import NLS.KdV.HillRadiusRootProduct
import NLS.ComplexAnalysis.NativeOwnPeriodSubtraction
/-! # Native Hilbert regular gap numerators with the own unit term removed

The actual normalized family and filled root give one jointly analytic,
uniformly bounded output Hilbert numerator on the filled energy discs.
The complete genuine Bochner period is zero, including the own mode.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

def hillNativeRegularGapNumerator (G : ℂ × Coeff 2 → Coeff 2) (k : ℕ+) (t : ℂ × Coeff 2) : Coeff 2 :=
  (-I/hillFilledFreeGapRoot h0q h0r (k : ℕ) (t.1,Coeff.periodDouble t.2)) • G t-lp.single 2 (k : ℤ) 1

theorem exists_hillNative_regular_gap_numerators
    (η B : ℝ) (hη : 0 < η) (G : ℂ × Coeff 2 → Coeff 2)
    (hGa : AnalyticOnNhd ℂ G (univ ×ˢ ball (0 : Coeff 2) η))
    (hsource : ∀ u ∈ ball (0 : Coeff 2) η, Coeff.periodDouble u ∈ ball (0 : Coeff 2) B)
    (C : ℝ) (hC : 0 ≤ C)
    (hdata : ∀ u ∈ ball (0 : Coeff 2) η, ∀ k : ℕ+,
      (∀ E ∈ sphere (freeHillEnergy k) (k : ℝ),
        (E,periodOneL2Inclusion u) ∈ hillHminusContinuationDomain ∧
        ‖(hillHminusContinuedRoot (E,periodOneL2Inclusion u))⁻¹ • G (E,u)‖ ≤ C/(k : ℝ)) ∧
      CircleIntegrable (fun E : ℂ => (hillHminusContinuedRoot (E,periodOneL2Inclusion u))⁻¹ • G (E,u)) (freeHillEnergy k) (k : ℝ) ∧
      (2*(Real.pi : ℂ))⁻¹ • (∮ E in C(freeHillEnergy k,(k : ℝ)),
        (hillHminusContinuedRoot (E,periodOneL2Inclusion u))⁻¹ • G (E,u)) = lp.single 2 (k : ℤ) 1) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ M : ℝ, 0 < M ∧ ∀ k : ℕ+, N ≤ (k : ℕ) →
      AnalyticOnNhd ℂ (hillNativeRegularGapNumerator h0q h0r G k)
        (closedBall (freeHillEnergy k) (k : ℝ) ×ˢ ball (0 : Coeff 2) η) ∧
      ∀ u ∈ ball (0 : Coeff 2) η,
        (∀ E ∈ closedBall (freeHillEnergy k) (k : ℝ), ‖hillNativeRegularGapNumerator h0q h0r G k (E,u)‖ ≤ M) ∧
        CircleIntegrable (fun E : ℂ => (hillFreeGapQuadraticRoot h0q h0r (k : ℕ) (E,Coeff.periodDouble u))⁻¹ •
          hillNativeRegularGapNumerator h0q h0r G k (E,u)) (freeHillEnergy k) (k : ℝ) ∧
        (∮ E in C(freeHillEnergy k,(k : ℝ)), (hillFreeGapQuadraticRoot h0q h0r (k : ℕ) (E,Coeff.periodDouble u))⁻¹ •
          hillNativeRegularGapNumerator h0q h0r G k (E,u)) = 0 := by
  obtain ⟨Nm,hNm,hmatch⟩ := exists_hillRadiusEnergyCircle_root_product_matching h0q h0r η B hη hsource
    (fun u hu k E hE => ((hdata u hu k).1 E hE).1)
  obtain ⟨Nq,_,hQ⟩ := exists_hillRadiusEnergyCircle_quadratic_data h0q h0r B
  obtain ⟨Nu,_,hU⟩ := exists_hillFilledFreeGapRoot_bounded_complex_analytic h0q h0r B
  refine ⟨max Nm (max Nq Nu),hNm.trans (le_max_left _ _),2*C+1,by positivity,?_⟩
  intro k hk
  have hkm := (le_max_left Nm (max Nq Nu)).trans hk
  have hkq := (le_max_left Nq Nu).trans ((le_max_right Nm (max Nq Nu)).trans hk)
  have hku := (le_max_right Nq Nu).trans ((le_max_right Nm (max Nq Nu)).trans hk)
  obtain ⟨hc,hRlo,_⟩ := hillFreeGap_energy_radius_geometry h0q h0r k
  have hEold (E : ℂ) (hE : E ∈ closedBall (freeHillEnergy k) (k : ℝ)) :
      E ∈ closedBall (hillRealGapCenter 0 h0q h0r (k : ℕ) : ℂ)
        (hillRealGapHalfLength 0 h0q h0r (k : ℕ)+hillRealGapCollar 0 h0q h0r (k : ℕ)) := by
    rw [hc]
    exact closedBall_subset_closedBall hRlo hE
  let f := fun t : ℂ × Coeff 2 => (-I/hillFilledFreeGapRoot h0q h0r (k : ℕ) (t.1,Coeff.periodDouble t.2)) • G t
  have hf : AnalyticOnNhd ℂ f (closedBall (freeHillEnergy k) (k : ℝ) ×ˢ ball (0 : Coeff 2) η) := by
    intro t ht
    have hUt := (hU (k : ℕ) hku).1 (t.1,Coeff.periodDouble t.2) ⟨hEold t.1 ht.1,hsource t.2 ht.2⟩
    have hUa := hUt.comp (f := fun s : ℂ × Coeff 2 => (s.1,Coeff.periodDouble s.2))
      (analyticAt_fst.prod ((Coeff.periodDouble.toContinuousLinearMap.analyticAt t.2).comp analyticAt_snd))
    have hUn := ((hU (k : ℕ) hku).2 _ (hsource t.2 ht.2) t.1 (hEold t.1 ht.1)).2.1
    exact (analyticAt_const.div hUa hUn).smul (hGa t ⟨mem_univ _,ht.2⟩)
  refine ⟨?_,?_⟩
  · intro t ht
    exact (hf t ht).sub analyticAt_const
  · intro u hu
    let Q := fun E : ℂ => hillFreeGapQuadraticRoot h0q h0r (k : ℕ) (E,Coeff.periodDouble u)
    let U := fun E : ℂ => hillFilledFreeGapRoot h0q h0r (k : ℕ) (E,Coeff.periodDouble u)
    let S := fun E : ℂ => hillHminusContinuedRoot (E,periodOneL2Inclusion u)
    let e : Coeff 2 := lp.single 2 (k : ℤ) 1
    have hp := hsource u hu
    have hprod (E : ℂ) (hE : E ∈ sphere (freeHillEnergy k) (k : ℝ)) : Q E*U E=S E :=
      hmatch k hkm u hu E hE
    have hdist (E : ℂ) (hE : E ∈ sphere (freeHillEnergy k) (k : ℝ)) : (k : ℝ)/2 ≤ ‖E-freeHillEnergy k‖ := by
      rw [mem_sphere_iff_norm.mp hE]
      nlinarith [show (0 : ℝ) ≤ k by positivity]
    have hfslice : AnalyticOnNhd ℂ (fun E => (-I/U E) • G (E,u)) (closedBall (freeHillEnergy k) (k : ℝ)) := by
      intro E hE
      exact (hf (E,u) ⟨hE,hu⟩).comp (f := fun E : ℂ => (E,u)) (analyticAt_id.prod analyticAt_const)
    have hbound := norm_native_own_regular_numerator_le (fun E => G (E,u)) Q U S e (freeHillEnergy k) (k : ℝ) C
      (by positivity) hfslice hprod
      (fun E hE => ((hQ k hkq).2.1 _ hp E (hdist E hE)).2.1)
      (fun E hE => by simpa only [mem_sphere_iff_norm.mp hE] using ((hQ k hkq).2.1 _ hp E (hdist E hE)).2.2.2)
      (fun E hE => ((hdata u hu k).1 E hE).2)
    have hπ : (2*(Real.pi : ℂ)) ≠ 0 := mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)
    have hraw : (∮ E in C(freeHillEnergy k,(k : ℝ)), (S E)⁻¹ • G (E,u)) = (2*(Real.pi : ℂ)) • e := by
      have hh := congrArg (fun v : Coeff 2 => (2*(Real.pi : ℂ)) • v) (hdata u hu k).2.2
      simpa only [smul_smul,mul_inv_cancel₀ hπ,one_smul] using hh
    have hperiod := native_own_period_subtraction (fun E => G (E,u)) Q U S e (freeHillEnergy k) (k : ℝ)
      (by positivity) hprod (hdata u hu k).2.1 ((hQ k hkq).2.2 _ hp).1 hraw ((hQ k hkq).2.2 _ hp).2
    refine ⟨?_,hperiod⟩
    intro E hE
    change ‖(-I/U E) • G (E,u)-e‖ ≤ 2*C+1
    have he : ‖e‖ = 1 := by simp only [e,lp.norm_single (by norm_num : 0 < (2 : ENNReal)),norm_one]
    simpa only [he] using hbound E hE
end NLS.KdV
