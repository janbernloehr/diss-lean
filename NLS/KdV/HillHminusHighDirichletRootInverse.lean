import NLS.KdV.HillHminusHighRootPhysicalGerm
import NLS.KdV.HillHminusLocalDirichletRootInverse
import NLS.ComplexAnalysis.AnalyticZeroLinearBound

/-! # A common bounded rough inverse-root family at moving high divisors -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillHminus_high_moving_root_inverses
    (D : PeriodOneHminusOne → Coeff 2) (hD : AnalyticAt ℂ D 0) (hD0 : D 0=0)
    (hphysical : ∀ n : ℕ+, ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,h0q,h0r⟩,
      hillHminusMovingDirichletEnergy D n (hillPhysicalHminusEmbedding p).val=
        (hillDirichletEnergy p.val p.property.1 p.property.2 (n : ℕ) n.property : ℂ)) :
    ∃ η C : ℝ, ∃ N : ℕ, 0 < η ∧ 0 < C ∧ 2 ≤ N ∧ ∀ n : ℕ+, N ≤ (n : ℕ) →
      ∃ H : PeriodOneHminusOne → ℂ,
        AnalyticOnNhd ℂ H (ball (0 : PeriodOneHminusOne) η) ∧
        (∀ q ∈ ball (0 : PeriodOneHminusOne) η, ‖H q‖ ≤ C) ∧
        ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,h0q,h0r⟩,
          H (hillPhysicalHminusEmbedding p).val=
            ((n : ℂ)*hillDeflatedEnergyCanonicalRoot p.val p.property.1 p.property.2 (n : ℕ)
              (hillDirichletEnergy p.val p.property.1 p.property.2 (n : ℕ) n.property))⁻¹ := by
  obtain ⟨rD,CD,hrD,hCD,hDa,hDb⟩ := exists_analytic_zero_linear_bound D hD hD0
  obtain ⟨r,C,N,V,hr,_hrpi,hC,hN,hV,h0V,hfamily⟩ :=
    exists_hillHminus_free_normalized_high_roots h0q h0r
  obtain ⟨rV,hrV,hsubV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds h0V)
  let η : ℝ := min rD (min rV (Real.pi*r/CD))
  have hη : 0 < η := lt_min hrD (lt_min hrV (by positivity))
  have hηD : η ≤ rD := min_le_left _ _
  have hηV : η ≤ rV := (min_le_right _ _).trans (min_le_left _ _)
  have hηs : η ≤ Real.pi*r/CD := (min_le_right _ _).trans (min_le_right _ _)
  have hsource (q : PeriodOneHminusOne) (hq : q ∈ ball 0 η) : q ∈ V :=
    hsubV (ball_subset_ball hηV hq)
  have hsmall (q : PeriodOneHminusOne) (hq : q ∈ ball 0 η) : ‖D q‖ < Real.pi*r := by
    have hnq := (mem_ball_zero_iff.mp hq).trans_le hηs
    have hc : CD*(Real.pi*r/CD)=Real.pi*r := by field_simp
    calc
      ‖D q‖ ≤ CD*‖q‖ := hDb q (ball_subset_ball hηD hq)
      _ < CD*(Real.pi*r/CD) := mul_lt_mul_of_pos_left hnq hCD
      _ = _ := hc
  have hinside (n : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ ball 0 η) :
      (hillHminusMovingDirichletEnergy D n q,q) ∈
        ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) ×ˢ V := by
    refine ⟨?_,hsource q hq⟩
    rw [mem_ball_iff_norm]
    simp only [hillHminusMovingDirichletEnergy,add_sub_cancel_left,norm_mul,
      show ‖(n : ℂ)‖=(n : ℝ) by simp]
    calc
      (n : ℝ)*‖D q (n : ℤ)‖ ≤ (n : ℝ)*‖D q‖ := mul_le_mul_of_nonneg_left
        (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) (D q) (n : ℤ)) (by positivity)
      _ < (n : ℝ)*(Real.pi*r) := mul_lt_mul_of_pos_left (hsmall q hq) (by positivity)
      _ = _ := by ring
  refine ⟨η,C,N,hη,hC,hN,?_⟩
  intro n hn
  have hn2 : 2 ≤ (n : ℕ) := hN.trans hn
  obtain ⟨U,hUa,hpairs,hU0,hprops⟩ := hfamily n hn
  let H : PeriodOneHminusOne → ℂ := fun q => (U (hillHminusMovingDirichletEnergy D n q,q))⁻¹
  refine ⟨H,?_,?_,?_⟩
  · intro q hq
    have hEq := analyticAt_hillHminusMovingDirichletEnergy D n q (hDa q (ball_subset_ball hηD hq))
    exact ((hUa (hillHminusMovingDirichletEnergy D n q,q) (hinside n q hq)).comp
      (f := fun q => (hillHminusMovingDirichletEnergy D n q,q))
      (hEq.prod analyticAt_id)).inv (hprops _ (hinside n q hq)).1
  · intro q hq
    exact (hprops _ (hinside n q hq)).2.1
  · filter_upwards [hphysical n,hillHminus_high_root_dirichlet_physical_germ h0q h0r n hn2 r hr
      V hV h0V hpairs U hUa hU0 (fun t ht => (hprops t ht).2.2)] with p hpD hpU
    have hnn : (n : ℂ)≠0 := by exact_mod_cast n.ne_zero
    have hu := (div_eq_iff hnn).mp hpU
    calc
      H (hillPhysicalHminusEmbedding p).val=
          (U ((hillDirichletEnergy p.val p.property.1 p.property.2 (n : ℕ) n.property : ℂ),
            (hillPhysicalHminusEmbedding p).val))⁻¹ :=
        congrArg (fun z : ℂ => (U (z,(hillPhysicalHminusEmbedding p).val))⁻¹) hpD
      _ = _ := congrArg Inv.inv (hu.trans (mul_comm _ _))

end NLS.KdV
