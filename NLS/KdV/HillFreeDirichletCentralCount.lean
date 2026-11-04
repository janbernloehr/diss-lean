import NLS.KdV.HillScaledFreeZeroCounts
import NLS.KdV.HillDirichletCharacteristicExterior

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



theorem hillL2DirichletCharacteristic_free_zero_iff (E : ℂ) :
    hillL2DirichletCharacteristic 0 E=0 ↔ ∃ n : ℕ, 1≤n ∧ E=(freeHillValue n : ℂ) := by
  constructor
  · intro hzero
    obtain ⟨n,rfl⟩ := (hillL2Radicand_free_zero_iff E).mp
      (hillL2DirichletCharacteristic_free_zero_imp_radicand E hzero)
    have hn : n≠0 := by
      intro he
      subst n
      norm_num [freeHillValue,hillL2DirichletCharacteristic_free_zero] at hzero
    exact ⟨n,by omega,rfl⟩
  · rintro ⟨n,hn,rfl⟩
    have he : (freeHillValue n : ℂ)=((n : ℂ)*Real.pi)^2 := by
      simp only [freeHillValue,Int.cast_natCast,ofReal_mul,ofReal_pow,ofReal_natCast]
      ring
    rw [he]
    exact hillL2DirichletCharacteristic_free_nat_root n hn

theorem freeHillValue_mem_energy_centralDisc_iff (k n : ℕ) :
    (freeHillValue n : ℂ)∈closedBall (0 : ℂ) ((centralCircleRadius k)^2) ↔ n≤k := by
  rw [mem_closedBall,dist_zero_right,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (show 0≤freeHillValue n by unfold freeHillValue;positivity)]
  have hn : 0≤(n : ℝ) := Nat.cast_nonneg n
  have hk : 0≤(k : ℝ) := Nat.cast_nonneg k
  have hpi : 0<Real.pi := Real.pi_pos
  have hpn : 0≤Real.pi*(n : ℝ) := mul_nonneg hpi.le hn
  have hpk : 0<Real.pi*(k : ℝ)+Real.pi/2 := by positivity
  change Real.pi^2*(n : ℝ)^2≤((k : ℝ)*Real.pi+Real.pi/2)^2 ↔ _
  constructor
  · intro h
    by_contra hh
    have hnr : (k : ℝ)+1≤n := by exact_mod_cast (by omega : k+1≤n)
    have hgap : (k : ℝ)*Real.pi+Real.pi/2<Real.pi*(n : ℝ) := by nlinarith
    nlinarith [mul_pos (sub_pos.mpr hgap) (show 0<Real.pi*(n : ℝ)+((k : ℝ)*Real.pi+Real.pi/2) by positivity)]
  · intro h
    have hnk : (n : ℝ)≤k := by exact_mod_cast h
    have hle : Real.pi*(n : ℝ)≤(k : ℝ)*Real.pi+Real.pi/2 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hle) (show 0≤Real.pi*(n : ℝ)+((k : ℝ)*Real.pi+Real.pi/2) by positivity)]

/-- The free Dirichlet characteristic has exactly k simple zeros in
the central energy circle of radius ((k+1/2)*pi)^2. -/
theorem hillL2DirichletCharacteristic_free_central_count (k : ℕ) :
    analyticZeroCount (hillL2DirichletCharacteristic 0)
      (closedBall (0 : ℂ) ((centralCircleRadius k)^2))=k := by
  let S := (Finset.Icc 1 k).image (fun n : ℕ => (freeHillValue n : ℂ))
  have hs : (S : Set ℂ)⊆closedBall (0 : ℂ) ((centralCircleRadius k)^2) := by
    intro E hE
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hE
    exact (freeHillValue_mem_energy_centralDisc_iff k n).mpr (Finset.mem_Icc.mp hn).2
  have hcover : closedBall (0 : ℂ) ((centralCircleRadius k)^2) ∩
      (hillL2DirichletCharacteristic 0) ⁻¹' {0}⊆S := by
    rintro E ⟨hE,hzero⟩
    obtain ⟨n,hn,rfl⟩ := (hillL2DirichletCharacteristic_free_zero_iff E).mp hzero
    exact Finset.mem_image.mpr ⟨n,Finset.mem_Icc.mpr
      ⟨hn,(freeHillValue_mem_energy_centralDisc_iff k n).mp hE⟩,rfl⟩
  rw [analyticZeroCount_eq_sum S hs hcover]
  dsimp only [S]
  rw [Finset.sum_image]
  · have ho (n : ℕ) (hn : n∈Finset.Icc 1 k) :
        analyticOrderNatAt (hillL2DirichletCharacteristic 0) (freeHillValue n : ℂ)=1 :=
      analyticOrderNatAt_hillL2Dirichlet_zero 0 (by intro j;simp)
        (freeHillValue n) ((hillL2DirichletCharacteristic_free_zero_iff _).mpr
          ⟨n,(Finset.mem_Icc.mp hn).1,rfl⟩)
    rw [Finset.sum_congr rfl ho]
    simp
  · intro a _ b _ he
    exact strictMono_freeHillValue.injective (Complex.ofReal_injective he)

end NLS.KdV
