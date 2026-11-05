import NLS.ComplexAnalysis.AnalyticLinearSourcePullback
import NLS.Articles.KdVKdV2Frequencies.NativeNormalizedDensity
import NLS.KdV.HillMiuraPhysicalProductDecay
import NLS.KdV.HillFrequencyPhysicalPeriodTransfer
import NLS.KdV.HillAbelianCoordinateContinuity

/-! # Uniform full Hilbert density bounds for the actual physical family

One complex L2 ball supports the native analytic normalized numerator family,
its actual physical identification, exact vector periods, and C/k density
bounds before all inner contours and all output indices, including the own mode.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

private theorem zero_parity : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0 := by
  rw [map_zero]
  exact Submodule.zero_mem _

private theorem zero_real : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)) := by
  rw [map_zero]
  intro k
  simp

/-- The physical normalized numerators have one native analytic complex
extension whose complete output-index Hilbert density norm is at most C/k
on every inner frequency contour. The source ball precedes all indices. -/
theorem exists_hillPhysical_normalized_numerators_uniform_density :
    ∃ η : ℝ, ∃ G : ℂ × Coeff 2 → Coeff 2,
      0 < η ∧ AnalyticOnNhd ℂ G (univ ×ˢ ball (0 : Coeff 2) η) ∧
      (∀ n : ℕ+, ∀ E : ℂ, G (E,0) (n : ℤ) = classicalHillFreePsi n E) ∧
      (∀ t ∈ univ ×ˢ ball (0 : Coeff 2) η, ∀ m : ℤ, m ≤ 0 → G t m = 0) ∧
      (∀ u ∈ ball (0 : Coeff 2) η, ∀ k : ℕ+,
        CircleIntegrable (fun z : ℂ => ((2*z)/hillHminusContinuedRoot (z^2,periodOneL2Inclusion u)) • G (z^2,u))
          ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4) ∧
        (2*(Real.pi : ℂ))⁻¹ • (∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
          ((2*z)/hillHminusContinuedRoot (z^2,periodOneL2Inclusion u)) • G (z^2,u)) = lp.single 2 (k : ℤ) 1) ∧
      (∃ K : ℝ, 0 < K ∧ ∀ u ∈ ball (0 : Coeff 2) η, ∀ k : ℕ+,
        ∀ z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/8),
          (z^2,periodOneL2Inclusion u) ∈ hillHminusContinuationDomain ∧
          ‖(hillHminusContinuedRoot (z^2,periodOneL2Inclusion u))⁻¹ • G (z^2,u)‖ ≤ K/(k : ℝ)) ∧
      ∀ p : RealHillWeightedPotential SpectralWeight.one,
        SpectralWeight.one.doubleIndex.toCoeff p.val ∈ ball (0 : Coeff 2) η →
        ∀ n : ℕ+, ∀ E : ℂ,
          G (E,SpectralWeight.one.doubleIndex.toCoeff p.val) (n : ℤ) =
            hillAbelianSelectedGlobalPsi (hillRealWeightedEmbedding SpectralWeight.one p).val
              (hillRealWeightedEmbedding SpectralWeight.one p).property.1
              (hillRealWeightedEmbedding SpectralWeight.one p).property.2 (n : ℕ) n.property E := by
  obtain ⟨C,δ,W₀,W,s,F,hδ,hδC,_,_,hFa,hmatch,hfree,hzero,hperiod,K,hK,hbound⟩ :=
    exists_hillHminus_actual_native_normalized_density
  obtain ⟨C',N,V,_,D⟩ := exists_hillHminus_all_contour_period_data
  obtain ⟨ε,B,hε,_,hc⟩ := exists_hillComplexPeriodControl zero_parity zero_real
  obtain ⟨η,hη,hsources⟩ := exists_common_ball_linear_preimage periodOneL2Inclusion δ ε hδ hε V D.isOpen D.zero_mem
  let G : ℂ × Coeff 2 → Coeff 2 := fun t => F (t.1,periodOneL2Inclusion t.2)
  have hGa : AnalyticOnNhd ℂ G (univ ×ˢ ball (0 : Coeff 2) η) :=
    analyticOnNhd_product_linear_pullback periodOneL2Inclusion δ η F hFa (fun u hu => (hsources u hu).1)
  refine ⟨η,G,hη,hGa,?_,?_,?_,?_,?_⟩
  · intro n E
    dsimp only [G]
    rw [map_zero]
    exact hfree n E
  · intro t ht m hm
    change F (t.1,periodOneL2Inclusion t.2) m = 0
    exact hzero (t.1,periodOneL2Inclusion t.2) ⟨mem_univ _,(hsources t.2 ht.2).1⟩ m hm
  · intro u hu k
    exact hperiod k _ (hsources u hu).1
  · refine ⟨K,hK,?_⟩
    intro u hu k z hz
    exact hbound (periodOneL2Inclusion u) (hsources u hu).1 k z hz
  · intro p hp n E
    let q := hillRealWeightedEmbedding SpectralWeight.one p
    let u := SpectralWeight.one.doubleIndex.toCoeff p.val
    have hδu : periodOneL2Inclusion u ∈ ball (0 : PeriodOneHminusOne) δ := (hsources u hp).1
    have hVu : periodOneL2Inclusion u ∈ V := (hsources u hp).2.1
    have hcoeff : SpectralWeight.one.toCoeff q.val = Coeff.periodDouble u := by
      dsimp only [q,hillRealWeightedEmbedding,u]
      rw [toCoeff_hillPeriodOneUnitPotential,toCoeff_hillPeriodOnePotential]
    have hsmall : ‖SpectralWeight.one.toCoeff q.val‖ ≤ ε := by
      rw [hcoeff,Coeff.norm_periodDouble]
      exact (hsources u hp).2.2
    have hFenergy : AnalyticOnNhd ℂ (fun E => F (E,periodOneL2Inclusion u)) univ := by
      intro E _
      exact (hFa (E,periodOneL2Inclusion u) ⟨mem_univ _,hδu⟩).comp
        (f := fun z : ℂ => (z,periodOneL2Inclusion u)) (analyticAt_id.prod analyticAt_const)
    have hphys := hillHminus_native_vector_periods_give_physical_periods zero_parity zero_real C' D ε B hc
      q.val q.property.1 q.property.2 hsmall u hcoeff hVu
      (fun E => F (E,periodOneL2Inclusion u)) hFenergy (fun k => hperiod k _ hδu) n
    have hFn : (fun E => F (E,periodOneL2Inclusion u) (n : ℤ)) =
        (fun E => hillHminusMiuraEnergyPsi C s (n : ℤ) (E,periodOneL2Inclusion u)) :=
      funext (fun E => hmatch _ hδu n E)
    rw [hFn] at hphys
    have heq := (hillHminusMiuraEnergyPsi_eq_selected_iff_periods q.val q.property.1 q.property.2
      C s (n : ℕ) n.property u hcoeff (hδC hδu)).mpr hphys
    change F (E,periodOneL2Inclusion u) (n : ℤ) = _
    rw [hmatch _ hδu n]
    exact congrFun heq E

end NLS.Articles.KdVKdV2Frequencies
