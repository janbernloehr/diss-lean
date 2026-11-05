import NLS.Articles.KdVKdV2Frequencies.PhysicalEnergyContours
import NLS.KdV.HillAllNativeRegularGapNumerators
import NLS.KdV.HillAllNativeQuadraticSolutions

/-! # Native regular filling for every positive Hill gap

The finite regular head and the uniform tail share one complex period-one
L2 ball. The actual normalized physical numerator gives native regular
numerators and filled quadratic solutions before all gaps and outputs.
Moving terminal evaluation and physical correction identification for the
remaining finite head are separate obligations.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

private theorem zero_parity : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0 := by
  rw [map_zero]
  exact Submodule.zero_mem _
private theorem zero_real : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)) := by
  rw [map_zero]
  intro k
  simp

theorem exists_hillPhysical_native_all_regular_gap_solutions :
    ∃ η : ℝ, ∃ G : ℂ × Coeff 2 → Coeff 2,
      ∃ H : ℕ+ → ℂ × Coeff 2 → Coeff 2, ∃ M : ℝ,
      0 < η ∧ 0 < M ∧ AnalyticOnNhd ℂ G (univ ×ˢ ball (0 : Coeff 2) η) ∧
      (∀ k : ℕ+,
        AnalyticOnNhd ℂ (hillNativeRegularGapNumerator zero_parity zero_real G k)
          (closedBall (freeHillEnergy k) (k : ℝ) ×ˢ ball (0 : Coeff 2) η) ∧
        (∀ u ∈ ball (0 : Coeff 2) η,
          (∀ E ∈ closedBall (freeHillEnergy k) (k : ℝ), ‖hillNativeRegularGapNumerator zero_parity zero_real G k (E,u)‖ ≤ M) ∧
          (∀ E ∈ closedBall (freeHillEnergy k) (k : ℝ), ∀ j : ℤ, j ≤ 0 →
            hillNativeRegularGapNumerator zero_parity zero_real G k (E,u) j = 0) ∧
          CircleIntegrable (fun E : ℂ =>
            (hillFreeGapQuadraticRoot zero_parity zero_real (k : ℕ) (E,Coeff.periodDouble u))⁻¹ •
              hillNativeRegularGapNumerator zero_parity zero_real G k (E,u)) (freeHillEnergy k) (k : ℝ) ∧
          (∮ E in C(freeHillEnergy k,(k : ℝ)),
            (hillFreeGapQuadraticRoot zero_parity zero_real (k : ℕ) (E,Coeff.periodDouble u))⁻¹ •
              hillNativeRegularGapNumerator zero_parity zero_real G k (E,u)) = 0) ∧
        AnalyticOnNhd ℂ (H k)
          (ball (freeHillEnergy k) (3*(k : ℝ)/4) ×ˢ ball (0 : Coeff 2) η) ∧
        (∀ u ∈ ball (0 : Coeff 2) η, ∀ E ∈ ball (freeHillEnergy k) (3*(k : ℝ)/4),
          hillLocalGapPolynomial 0 zero_parity zero_real (k : ℕ) (Coeff.periodDouble u) E •
              deriv (fun z => H k (z,u)) E +
            (E-hillLocalGapMidpoint 0 zero_parity zero_real (k : ℕ) (Coeff.periodDouble u)) • H k (E,u) =
              hillNativeRegularGapNumerator zero_parity zero_real G k (E,u)) ∧
        ∀ u ∈ ball (0 : Coeff 2) η, ∀ E ∈ closedBall (freeHillEnergy k) ((k : ℝ)/4),
          ‖H k (E,u)‖ ≤ 18*Real.pi*M/(k : ℝ)) ∧
      ∀ p : RealHillWeightedPotential SpectralWeight.one,
        SpectralWeight.one.doubleIndex.toCoeff p.val ∈ ball (0 : Coeff 2) η →
        let q := hillRealWeightedEmbedding SpectralWeight.one p
        let u := SpectralWeight.one.doubleIndex.toCoeff p.val
        ∀ n : ℕ+, ∀ E : ℂ, G (E,u) (n : ℤ) =
          hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 (n : ℕ) n.property E := by
  obtain ⟨ρ,G,hρ,hGa,_,hzero,_,⟨C,hC,henergy⟩,hphysical⟩ := exists_hillPhysical_native_energy_contours
  obtain ⟨εg,hεg,hgreg⟩ := exists_hillNative_all_regular_gap_numerators zero_parity zero_real
  obtain ⟨εh,hεh,hquadratic⟩ := exists_hillRadius_all_native_quadratic_solutions zero_parity zero_real
  let η := min ρ (min εg εh)
  have hη : 0 < η := lt_min hρ (lt_min hεg hεh)
  have hsub : ball (0 : Coeff 2) η ⊆ ball (0 : Coeff 2) ρ := ball_subset_ball (min_le_left _ _)
  have hηg : η ≤ εg := (min_le_right _ _).trans (min_le_left _ _)
  have hηh : η ≤ εh := (min_le_right _ _).trans (min_le_right _ _)
  have hGaη := hGa.mono (prod_mono Subset.rfl hsub)
  obtain ⟨M,hM,hreg⟩ := hgreg η hη hηg G hGaη C hC.le
    (fun u hu k => (henergy u (hsub hu) k).2)
  have hsol (k : ℕ+) := hquadratic η hηh k
    (hillNativeRegularGapNumerator zero_parity zero_real G k) M hM.le (hreg k).1
    (fun u hu => ((hreg k).2 u hu).1) (fun u hu => ((hreg k).2 u hu).2.2)
  choose H hHa hHeq hHb using hsol
  refine ⟨η,G,H,M,hη,hM,hGaη,?_,?_⟩
  · intro k
    refine ⟨(hreg k).1,?_,hHa k,hHeq k,hHb k⟩
    intro u hu
    refine ⟨((hreg k).2 u hu).1,?_,((hreg k).2 u hu).2⟩
    intro E _ j hj
    have hz := hzero (E,u) ⟨mem_univ _,hsub hu⟩ j hj
    have hkj : (0 : ℤ) < (k : ℤ) := by exact_mod_cast k.pos
    change (-I/hillFilledFreeGapRoot zero_parity zero_real (k : ℕ) (E,Coeff.periodDouble u))*G (E,u) j -
      (lp.single 2 (k : ℤ) (1 : ℂ) : Coeff 2) j = 0
    rw [hz,mul_zero]
    simp only [lp.single_apply,Pi.single_apply,if_neg (by omega : j ≠ (k : ℤ)),sub_self]
  · intro p hp
    exact (hphysical p (hsub hp)).2

end NLS.Articles.KdVKdV2Frequencies
