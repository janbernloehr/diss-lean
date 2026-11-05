import NLS.Articles.KdVKdV2Frequencies.PhysicalEnergyContours
import NLS.KdV.HillNativeRegularGapNumerator
import NLS.KdV.HillFilledFreeGapPhysical
/-! # Actual native physical regular numerators with own-period subtraction

One common complex L2 ball and one cutoff precede all high gap indices
and all output coordinates. The regular family is jointly native analytic
on filled discs, uniformly Hilbert bounded, and has zero Bochner period.
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

/-- The actual physical deflated differential minus the own Kronecker
term has a common native complex analytic Hilbert realization on filled
high energy discs, with one full norm bound and zero Bochner periods. -/
theorem exists_hillPhysical_native_regular_gap_numerators :
    ∃ η : ℝ, ∃ G : ℂ × Coeff 2 → Coeff 2, ∃ N : ℕ, ∃ M : ℝ,
      0 < η ∧ 1 ≤ N ∧ 0 < M ∧ AnalyticOnNhd ℂ G (univ ×ˢ ball (0 : Coeff 2) η) ∧
      (∀ u ∈ ball (0 : Coeff 2) η, ∀ k : ℕ+,
        (∀ E ∈ closedBall (freeHillEnergy k) (k : ℝ), ‖G (E,u)‖ ≤ M/(k : ℝ)) ∧
        (∀ E ∈ sphere (freeHillEnergy k) (k : ℝ),
          (E,periodOneL2Inclusion u) ∈ hillHminusContinuationDomain ∧
          ‖(hillHminusContinuedRoot (E,periodOneL2Inclusion u))⁻¹ • G (E,u)‖ ≤ M/(k : ℝ)) ∧
        CircleIntegrable (fun E : ℂ => (hillHminusContinuedRoot (E,periodOneL2Inclusion u))⁻¹ • G (E,u)) (freeHillEnergy k) (k : ℝ) ∧
        (2*(Real.pi : ℂ))⁻¹ • (∮ E in C(freeHillEnergy k,(k : ℝ)),
          (hillHminusContinuedRoot (E,periodOneL2Inclusion u))⁻¹ • G (E,u)) = lp.single 2 (k : ℤ) 1) ∧
      (∀ k : ℕ+, N ≤ (k : ℕ) →
        AnalyticOnNhd ℂ (hillNativeRegularGapNumerator zero_parity zero_real G k)
          (closedBall (freeHillEnergy k) (k : ℝ) ×ˢ ball (0 : Coeff 2) η) ∧
        ∀ u ∈ ball (0 : Coeff 2) η,
          (∀ E ∈ closedBall (freeHillEnergy k) (k : ℝ), ‖hillNativeRegularGapNumerator zero_parity zero_real G k (E,u)‖ ≤ M) ∧
          (∀ E ∈ closedBall (freeHillEnergy k) (k : ℝ), ∀ j : ℤ, j ≤ 0 →
            hillNativeRegularGapNumerator zero_parity zero_real G k (E,u) j=0) ∧
          CircleIntegrable (fun E : ℂ => (hillFreeGapQuadraticRoot zero_parity zero_real (k : ℕ) (E,Coeff.periodDouble u))⁻¹ •
            hillNativeRegularGapNumerator zero_parity zero_real G k (E,u)) (freeHillEnergy k) (k : ℝ) ∧
          (∮ E in C(freeHillEnergy k,(k : ℝ)), (hillFreeGapQuadraticRoot zero_parity zero_real (k : ℕ) (E,Coeff.periodDouble u))⁻¹ •
            hillNativeRegularGapNumerator zero_parity zero_real G k (E,u)) = 0) ∧
      ∀ p : RealHillWeightedPotential SpectralWeight.one,
        SpectralWeight.one.doubleIndex.toCoeff p.val ∈ ball (0 : Coeff 2) η →
        let q := hillRealWeightedEmbedding SpectralWeight.one p
        let u := SpectralWeight.one.doubleIndex.toCoeff p.val
        (∀ n : ℕ+, ∀ E : ℂ, G (E,u) (n : ℤ)=
          hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 (n : ℕ) n.property E) ∧
        ∀ k : ℕ+, N ≤ (k : ℕ) → ∀ n : ℕ+, ∀ E ∈ closedBall (freeHillEnergy k) (k : ℝ),
          hillNativeRegularGapNumerator zero_parity zero_real G k (E,u) (n : ℤ)=
            (-I)*hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 (n : ℕ) n.property E /
              hillDeflatedEnergyCanonicalRoot q.val q.property.1 q.property.2 (k : ℕ) E - (if k=n then 1 else 0) := by
  obtain ⟨ρ,G,hρ,hGa,_,hzero,_,⟨C,hC,henergy⟩,hphysical⟩ := exists_hillPhysical_native_energy_contours
  let η := min ρ (1/2)
  have hη : 0 < η := lt_min hρ (by norm_num)
  have hsub : ball (0 : Coeff 2) η ⊆ ball (0 : Coeff 2) ρ := ball_subset_ball (min_le_left _ _)
  have hsource (u : Coeff 2) (hu : u ∈ ball 0 η) : Coeff.periodDouble u ∈ ball (0 : Coeff 2) 1 := by
    rw [mem_ball_zero_iff,Coeff.norm_periodDouble]
    exact (mem_ball_zero_iff.mp hu).trans_le ((min_le_right ρ (1/2)).trans (by norm_num))
  have hGη := hGa.mono (prod_mono Subset.rfl hsub)
  obtain ⟨N,hN,M,hM,hreg⟩ := exists_hillNative_regular_gap_numerators zero_parity zero_real η 1 hη G hGη hsource C hC.le
    (fun u hu k => (henergy u (hsub hu) k).2)
  obtain ⟨Np,_,hUp⟩ := exists_hillFilledFreeGapRoot_bounded_real_physical_matching zero_parity zero_real 1
  refine ⟨η,G,max N Np,max M C,hη,hN.trans (le_max_left _ _),hM.trans_le (le_max_left _ _),hGη,?_,?_,?_⟩
  · intro u hu k
    have hd := henergy u (hsub hu) k
    have hscale : C/(k : ℝ) ≤ max M C/(k : ℝ) := div_le_div_of_nonneg_right (le_max_right _ _) (by positivity)
    exact ⟨fun E hE => (hd.1 E hE).trans hscale,fun E hE => ⟨(hd.2.1 E hE).1,((hd.2.1 E hE).2).trans hscale⟩,hd.2.2⟩
  · intro k hk
    have hkn := (le_max_left N Np).trans hk
    refine ⟨(hreg k hkn).1,?_⟩
    intro u hu
    have hd := (hreg k hkn).2 u hu
    refine ⟨fun E hE => (hd.1 E hE).trans (le_max_left _ _),?_,hd.2⟩
    intro E _ j hj
    have hz := hzero (E,u) ⟨mem_univ _,hsub hu⟩ j hj
    have hkj : (0 : ℤ) < (k : ℤ) := by exact_mod_cast k.pos
    change (-I/hillFilledFreeGapRoot zero_parity zero_real (k : ℕ) (E,Coeff.periodDouble u))*G (E,u) j -
      (lp.single 2 (k : ℤ) (1 : ℂ) : Coeff 2) j=0
    rw [hz,mul_zero]
    simp only [lp.single_apply,Pi.single_apply,if_neg (by omega : j ≠ (k : ℤ)),sub_self]
  · intro p hp
    let q := hillRealWeightedEmbedding SpectralWeight.one p
    let u := SpectralWeight.one.doubleIndex.toCoeff p.val
    have hcoeff : SpectralWeight.one.toCoeff q.val=Coeff.periodDouble u := by
      dsimp only [q,hillRealWeightedEmbedding,u]
      rw [toCoeff_hillPeriodOneUnitPotential,toCoeff_hillPeriodOnePotential]
    have hsmall : ‖SpectralWeight.one.toCoeff q.val‖ ≤ 1 := by
      rw [hcoeff]
      exact (mem_ball_zero_iff.mp (hsource u hp)).le
    refine ⟨(hphysical p (hsub hp)).2,?_⟩
    intro k hk n E hE
    obtain ⟨hc,hRlo,_⟩ := hillFreeGap_energy_radius_geometry zero_parity zero_real k
    have hEold : E ∈ closedBall (hillRealGapCenter 0 zero_parity zero_real (k : ℕ) : ℂ)
        (hillRealGapHalfLength 0 zero_parity zero_real (k : ℕ)+hillRealGapCollar 0 zero_parity zero_real (k : ℕ)) := by
      rw [hc]
      exact closedBall_subset_closedBall hRlo hE
    have hU := hUp q.val q.property.1 q.property.2 hsmall (k : ℕ) ((le_max_right N Np).trans hk) E hEold
    conv_lhs at hU => rw [hcoeff]
    change (-I/hillFilledFreeGapRoot zero_parity zero_real (k : ℕ) (E,Coeff.periodDouble u))*G (E,u) (n : ℤ) -
      (lp.single 2 (k : ℤ) (1 : ℂ) : Coeff 2) (n : ℤ) = _
    rw [hU,(hphysical p (hsub hp)).2 n E]
    simp only [lp.single_apply,Pi.single_apply]
    by_cases hkn : k=n
    · subst n
      simp only [ite_true]
      ring
    · have hne : (n : ℤ) ≠ (k : ℤ) := by
        intro he
        apply hkn
        exact_mod_cast he.symm
      rw [if_neg hne,if_neg hkn]
      ring
end NLS.Articles.KdVKdV2Frequencies
