import NLS.KdV.HillHminusDirichletEnergySequence
import NLS.KdV.HillHminusDirichletNormingSequence
import NLS.KdV.HillHminusNormingSinhIdentity
import NLS.ComplexAnalysis.AnalyticZeroLinearBound

/-! # Actual rough Dirichlet data in one native Hilbert analytic packet

The source is the original period-one Hminus-one space. One complex ball
precedes all Dirichlet indices and carries normalized energies, logarithmic
normings and their hyperbolic sines, with a genuine joint Hilbert norm bound.
This is spectral input for rough Abelian coordinates, not the full Birkhoff map.
-/
noncomputable section
open Set Metric Complex
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV NLS.ComplexAnalysis

private theorem zero_real : IsRealPeriodOneHminusOne 0 := by intro j; simp

theorem exists_hillHminus_native_dirichlet_packet :
    ∃ η C : ℝ, ∃ D K S : PeriodOneHminusOne → Coeff 2,
      0 < η ∧ 0 < C ∧
      AnalyticOnNhd ℂ D (ball (0 : PeriodOneHminusOne) η) ∧
      AnalyticOnNhd ℂ K (ball (0 : PeriodOneHminusOne) η) ∧
      AnalyticOnNhd ℂ S (ball (0 : PeriodOneHminusOne) η) ∧ D 0 = 0 ∧ K 0 = 0 ∧ S 0 = 0 ∧
      ∀ q ∈ ball (0 : PeriodOneHminusOne) η,
        ‖D q‖+‖K q‖+‖S q‖ ≤ C*‖q‖ ∧
        (∀ n : ℕ+, hillHminusDirichlet q (((Real.pi : ℂ)*(n : ℕ))^2+(n : ℂ)*D q (n : ℤ)) = 0) ∧
        (∀ hq : IsRealPeriodOneHminusOne q, ∀ n : ℕ+,
          D q (n : ℤ) = ((hillHminusDirichletEnergy q hq n : ℂ)-((Real.pi : ℂ)*(n : ℕ))^2)/(n : ℂ) ∧
          K q (n : ℤ) = (hillHminusDirichletLogNorming q hq n : ℂ) ∧
          S q (n : ℤ) = (Real.sinh (hillHminusDirichletLogNorming q hq n) : ℂ)) ∧
        (∀ j : ℤ, j ≤ 0 → D q j = 0 ∧ K q j = 0 ∧ S q j = 0) ∧
        ∀ j : ℤ, S q j = sinh (K q j) := by
  obtain ⟨V,D,hV,h0V,hDa,hroot,hDreal,hDnonpos⟩ :=
    exists_hillHminus_native_dirichlet_energy_sequence 0 zero_real
  obtain ⟨W,K,S,hW,h0W,hKa,hSa,hreal,hnonpos⟩ :=
    exists_hillHminus_native_dirichlet_norming_sequences 0 zero_real
  have hD0 : D 0 = 0 := by
    ext j
    change D 0 j = 0
    by_cases hj : 0 < j
    · let n : ℕ+ := ⟨j.toNat,by omega⟩
      have he : j = (n : ℤ) := by
          change j = (j.toNat : ℤ)
          exact (Int.toNat_of_nonneg hj.le).symm
      rw [he,hDreal 0 h0V zero_real n,hillHminusDirichletEnergy_zero_potential]
      have hf : (freeHillValue (n : ℕ) : ℂ) = ((Real.pi : ℂ)*(n : ℕ))^2 := by
        simp only [freeHillValue,ofReal_mul,ofReal_pow,Int.cast_natCast,ofReal_natCast]
        ring
      rw [hf,sub_self,zero_div]
    · exact hDnonpos 0 j (not_lt.mp hj)
  have hK0 : K 0 = 0 := by
    ext j
    change K 0 j = 0
    by_cases hj : 0 < j
    · let n : ℕ+ := ⟨j.toNat,by omega⟩
      have he : j = (n : ℤ) := by
          change j = (j.toNat : ℤ)
          exact (Int.toNat_of_nonneg hj.le).symm
      rw [he,(hreal 0 h0W zero_real n).1,hillHminusDirichletLogNorming_zero_potential,ofReal_zero]
    · exact (hnonpos 0 h0W j (not_lt.mp hj)).1
  have hS0 : S 0 = 0 := by
    ext j
    change S 0 j = 0
    by_cases hj : 0 < j
    · let n : ℕ+ := ⟨j.toNat,by omega⟩
      have he : j = (n : ℤ) := by
          change j = (j.toNat : ℤ)
          exact (Int.toNat_of_nonneg hj.le).symm
      rw [he,(hreal 0 h0W zero_real n).2,hillHminusDirichletLogNorming_zero_potential,Real.sinh_zero,ofReal_zero]
    · exact (hnonpos 0 h0W j (not_lt.mp hj)).2
  obtain ⟨rD,CD,hrD,hCD,hDr,hDb⟩ := exists_analytic_zero_linear_bound D (hDa 0 h0V) hD0
  obtain ⟨rK,CK,hrK,hCK,hKr,hKb⟩ := exists_analytic_zero_linear_bound K (hKa 0 h0W) hK0
  obtain ⟨rS,CS,hrS,hCS,hSr,hSb⟩ := exists_analytic_zero_linear_bound S (hSa 0 h0W) hS0
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp ((hV.inter hW).mem_nhds ⟨h0V,h0W⟩)
  let η := min r (min rD (min rK rS))
  have hη : 0 < η := lt_min hr (lt_min hrD (lt_min hrK hrS))
  have hηD : η ≤ rD := (min_le_right _ _).trans (min_le_left _ _)
  have hηK : η ≤ rK := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηS : η ≤ rS := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hU (q : PeriodOneHminusOne) (hq : q ∈ ball 0 η) : q ∈ V ∧ q ∈ W :=
    hball (ball_subset_ball (min_le_left _ _) hq)
  have hDη := hDr.mono (ball_subset_ball hηD)
  have hKη := hKr.mono (ball_subset_ball hηK)
  have hSη := hSr.mono (ball_subset_ball hηS)
  have hsinh := hillHminus_native_norming_sinh_identity η hη K S hKη hSη
    (fun q hq hqr n => hreal q (hU q hq).2 hqr n)
    (fun q hq j hj => hnonpos q (hU q hq).2 j hj)
  refine ⟨η,CD+CK+CS,D,K,S,hη,by positivity,hDη,hKη,hSη,hD0,hK0,hS0,?_⟩
  intro q hq
  refine ⟨?_,hroot q (hU q hq).1,?_,?_,hsinh q hq⟩
  · have hd := hDb q (ball_subset_ball hηD hq)
    have hk := hKb q (ball_subset_ball hηK hq)
    have hs := hSb q (ball_subset_ball hηS hq)
    calc
      _ ≤ CD*‖q‖+CK*‖q‖+CS*‖q‖ := add_le_add (add_le_add hd hk) hs
      _ = _ := by ring
  · intro hqr n
    exact ⟨hDreal q (hU q hq).1 hqr n,hreal q (hU q hq).2 hqr n⟩
  · intro j hj
    exact ⟨hDnonpos q j hj,hnonpos q (hU q hq).2 j hj⟩

end NLS.Articles.KdVKdV2Frequencies
