import NLS.KdV.HillHminusHighDirichletRootInverse
import NLS.SequenceSpaces.BoundedCoordinateAnalytic
import NLS.SequenceSpaces.PositiveFourierInverseMajorant

/-! # Native bounded inverse roots for every rough moving Dirichlet divisor -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillHminus_all_moving_root_inverses
    (D : PeriodOneHminusOne → Coeff 2) (hD : AnalyticAt ℂ D 0) (hD0 : D 0=0)
    (hphysical : ∀ n : ℕ+, ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,h0q,h0r⟩,
      hillHminusMovingDirichletEnergy D n (hillPhysicalHminusEmbedding p).val=
        (hillDirichletEnergy p.val p.property.1 p.property.2 (n : ℕ) n.property : ℂ)) :
    ∃ η C : ℝ, ∃ H : ℕ+ → PeriodOneHminusOne → ℂ, 0 < η ∧ 0 < C ∧ ∀ n : ℕ+,
      AnalyticOnNhd ℂ (H n) (ball (0 : PeriodOneHminusOne) η) ∧
      (∀ q ∈ ball (0 : PeriodOneHminusOne) η, ‖H n q‖ ≤ C) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,h0q,h0r⟩,
        H n (hillPhysicalHminusEmbedding p).val=
          ((n : ℂ)*hillDeflatedEnergyCanonicalRoot p.val p.property.1 p.property.2 (n : ℕ)
            (hillDirichletEnergy p.val p.property.1 p.property.2 (n : ℕ) n.property))⁻¹ := by
  classical
  obtain ⟨r,C,N,hr,hC,_hN,htail⟩ :=
    exists_hillHminus_high_moving_root_inverses h0q h0r D hD hD0 hphysical
  have hfinite (J : Finset ℕ+) : ∃ s B : ℝ, 0 < s ∧ 0 < B ∧ ∀ n ∈ J,
      AnalyticOnNhd ℂ (hillHminusLocalNormalizedRootInverse h0q h0r D n)
        (ball (0 : PeriodOneHminusOne) s) ∧
      ∀ q ∈ ball (0 : PeriodOneHminusOne) s, ‖hillHminusLocalNormalizedRootInverse h0q h0r D n q‖ ≤ B := by
    induction J using Finset.induction_on with
    | empty => exact ⟨1,1,by norm_num,by norm_num,fun n hn => (Finset.notMem_empty n hn).elim⟩
    | @insert n J hn ih =>
        obtain ⟨a,B,ha,hB,hna,hnb⟩ := exists_hillHminusLocalNormalizedRootInverse_analytic_bound h0q h0r D hD hD0 n
        obtain ⟨s,E,hs,hE,hJ⟩ := ih
        refine ⟨min a s,B+E,lt_min ha hs,add_pos hB hE,?_⟩
        intro m hm
        rcases Finset.mem_insert.mp hm with hm | hm
        · subst m
          exact ⟨hna.mono (ball_subset_ball (min_le_left a s)),
            fun q hq => (hnb q (ball_subset_ball (min_le_left a s) hq)).trans (by linarith)⟩
        · obtain ⟨hMa,hMb⟩ := hJ m hm
          exact ⟨hMa.mono (ball_subset_ball (min_le_right a s)),
            fun q hq => (hMb q (ball_subset_ball (min_le_right a s) hq)).trans (by linarith)⟩
  let J : Finset ℕ+ := (Finset.range N).image (fun k => (⟨k+1,by omega⟩ : ℕ+))
  obtain ⟨s,B,hs,hB,hhead⟩ := hfinite J
  let H : ℕ+ → PeriodOneHminusOne → ℂ := fun n =>
    if hn : N ≤ (n : ℕ) then Classical.choose (htail n hn)
    else hillHminusLocalNormalizedRootInverse h0q h0r D n
  refine ⟨min r s,C+B,H,lt_min hr hs,add_pos hC hB,?_⟩
  intro n
  by_cases hn : N ≤ (n : ℕ)
  · simp only [H,dif_pos hn]
    obtain ⟨ha,hb,hp⟩ := Classical.choose_spec (htail n hn)
    exact ⟨ha.mono (ball_subset_ball (min_le_left r s)),
      fun q hq => (hb q (ball_subset_ball (min_le_left r s) hq)).trans (by linarith),hp⟩
  · simp only [H,dif_neg hn]
    have hnJ : n ∈ J := by
      apply Finset.mem_image.mpr
      refine ⟨(n : ℕ)-1,Finset.mem_range.mpr (by omega),?_⟩
      apply Subtype.ext
      exact Nat.sub_add_cancel n.property
    obtain ⟨ha,hb⟩ := hhead n hnJ
    exact ⟨ha.mono (ball_subset_ball (min_le_right r s)),
      fun q hq => (hb q (ball_subset_ball (min_le_right r s) hq)).trans (by linarith),
      hillHminusLocalNormalizedRootInverse_physical_germ h0q h0r D n (hphysical n)⟩

theorem exists_hillHminus_native_moving_root_inverse
    (D : PeriodOneHminusOne → Coeff 2) (hD : AnalyticAt ℂ D 0) (hD0 : D 0=0)
    (hphysical : ∀ n : ℕ+, ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,h0q,h0r⟩,
      hillHminusMovingDirichletEnergy D n (hillPhysicalHminusEmbedding p).val=
        (hillDirichletEnergy p.val p.property.1 p.property.2 (n : ℕ) n.property : ℂ)) :
    ∃ η C : ℝ, ∃ M : PeriodOneHminusOne → Coeff ⊤,
      0 < η ∧ 0 < C ∧ AnalyticOnNhd ℂ M (ball (0 : PeriodOneHminusOne) η) ∧
      (∀ q ∈ ball (0 : PeriodOneHminusOne) η, ‖M q‖ ≤ C ∧ ∀ j : ℤ, j ≤ 0 → M q j=0) ∧
      ∀ n : ℕ+, ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,h0q,h0r⟩,
        M (hillPhysicalHminusEmbedding p).val (n : ℤ)=
          ((n : ℂ)*hillDeflatedEnergyCanonicalRoot p.val p.property.1 p.property.2 (n : ℕ)
            (hillDirichletEnergy p.val p.property.1 p.property.2 (n : ℕ) n.property))⁻¹ := by
  classical
  obtain ⟨η,C,H,hη,hC,hH⟩ := exists_hillHminus_all_moving_root_inverses h0q h0r D hD hD0 hphysical
  let a (q : PeriodOneHminusOne) : ℤ → ℂ := Coeff.positiveFamilyCoordinates (fun n => H n q)
  have hab (q : PeriodOneHminusOne) (hq : q ∈ ball 0 η) (j : ℤ) : ‖a q j‖ ≤ C := by
    by_cases hj : 0 < j
    · simpa only [a,Coeff.positiveFamilyCoordinates,dif_pos hj] using (hH (Coeff.positivePoleIndex j hj)).2.1 q hq
    · simp only [a,Coeff.positiveFamilyCoordinates,dif_neg hj,norm_zero]
      exact hC.le
  have hm (q : PeriodOneHminusOne) (hq : q ∈ ball 0 η) : Memℓp (a q) ⊤ :=
    memℓp_infty ⟨C,by rintro _ ⟨j,rfl⟩; exact hab q hq j⟩
  let M : PeriodOneHminusOne → Coeff ⊤ := fun q => Coeff.ofFunctionOrZero ⊤ (a q)
  have hval (q : PeriodOneHminusOne) (hq : q ∈ ball 0 η) (j : ℤ) : M q j=a q j :=
    Coeff.ofFunctionOrZero_apply_of_mem ⊤ _ (hm q hq) j
  have hb (q : PeriodOneHminusOne) (hq : q ∈ ball 0 η) : ‖M q‖ ≤ C := by
    apply lp.norm_le_of_forall_le hC.le
    intro j
    rw [hval q hq j]
    exact hab q hq j
  have ha (j : ℤ) : AnalyticOnNhd ℂ (fun q => M q j) (ball (0 : PeriodOneHminusOne) η) := by
    intro q hq
    have he : (fun u => a u j) =ᶠ[𝓝 q] (fun u => M u j) := by
      filter_upwards [isOpen_ball.mem_nhds hq] with u hu
      exact (hval u hu j).symm
    apply AnalyticAt.congr (f := fun u => a u j) ?_ he
    by_cases hj : 0 < j
    · simpa only [a,Coeff.positiveFamilyCoordinates,dif_pos hj] using (hH (Coeff.positivePoleIndex j hj)).1 q hq
    · simpa only [a,Coeff.positiveFamilyCoordinates,dif_neg hj] using
        (analyticAt_const (v := (0 : ℂ)) (𝕜 := ℂ) (x := q))
  refine ⟨η,C,M,hη,hC,Coeff.analyticOnNhd_of_bounded_coordinatewise M isOpen_ball ha C hb,?_,?_⟩
  · intro q hq
    refine ⟨hb q hq,?_⟩
    intro j hj
    rw [hval q hq j]
    simp only [a,Coeff.positiveFamilyCoordinates,dif_neg (not_lt.mpr hj)]
  · intro n
    have ht : Tendsto (fun p : RealPeriodOneHillPotential => hillOriginalHminusSource p.val)
        (𝓝 (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential)) (𝓝 (0 : PeriodOneHminusOne)) := by
      simpa only [Function.comp_def,map_zero] using
        (hillOriginalHminusSource.continuous.comp continuous_subtype_val).tendsto
          (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential)
    filter_upwards [(hH n).2.2,ht.eventually (ball_mem_nhds (0 : PeriodOneHminusOne) hη)] with p hp hpη
    have hq : (hillPhysicalHminusEmbedding p).val ∈ ball (0 : PeriodOneHminusOne) η := hpη
    rw [hval _ hq (n : ℤ)]
    change Coeff.positiveFamilyCoordinates (fun k => H k (hillPhysicalHminusEmbedding p).val) (n : ℤ)=_
    rw [Coeff.positiveFamilyCoordinates_nat]
    exact hp

end NLS.KdV
