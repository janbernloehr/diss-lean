import NLS.KdV.HillDirichletEnergyDisplacement
import NLS.KdV.HillUniformDirichletPhysical
import Mathlib.Analysis.RCLike.Sqrt

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

/-- The original physical high Dirichlet frequencies are positive real,
close to the free frequencies, and dominate the actual source norm,
uniformly on each bounded coefficient ball. -/
theorem exists_hillDirichletFrequency_uniform_high_control (B : ℝ) :
    ∃ N : ℕ, ∃ hN : 1≤N, ∀ q : RealPeriodOneHillPotential,
      ‖SpectralWeight.one.toCoeff q.val‖≤B → ∀ n : ℕ, ∀ hn : N≤n,
      let E := hillDirichletEnergy q.val q.property.1 q.property.2 n (hN.trans hn)
      let r := Real.sqrt E
      Complex.sqrt (E : ℂ)=(r : ℂ) ∧ 0<r ∧
        |r-(n : ℝ)*Real.pi|≤1/8 ∧ 32*‖SpectralWeight.one.toCoeff q.val‖≤r ∧ (n : ℝ)≤r := by
  obtain ⟨Nd,hNd,hdisp⟩ := exists_hillScaledDirichletRoot_energy_displacement_bound h0q h0r B
  obtain ⟨Np,hNp,hphysical⟩ := exists_hillScaledDirichletRoot_bounded_real_physical_matching
    h0q h0r (1/16) (by norm_num) (by norm_num) B
  obtain ⟨Ne,hNe⟩ := exists_nat_gt (192*(Real.exp (1/2))^2*B/Real.pi)
  obtain ⟨Ns,hNs⟩ := exists_nat_gt (64*B)
  refine ⟨Nd+Np+Ne+Ns+2,by omega,?_⟩
  intro q hq n hn
  have hnd : Nd≤n := by omega
  have hnp : Np≤n := by omega
  have hne : Ne≤n := by omega
  have hns : Ns≤n := by omega
  have hn1 : 1≤n := by omega
  have hnR : (1 : ℝ)≤n := by exact_mod_cast hn1
  let E := hillDirichletEnergy q.val q.property.1 q.property.2 n (by omega)
  let c : ℝ := (n : ℝ)*Real.pi
  let D : ℝ := 24*(Real.exp (1/2))^2*B
  have hc : 0<c := by dsimp only [c];positivity
  have hfree : (freeHillValue n : ℂ)=(c : ℂ)^2 := by
    simp only [freeHillValue,Int.cast_natCast,c]
    push_cast
    ring
  have hd : ‖(E : ℂ)-(c : ℂ)^2‖≤D := by
    have hh := hdisp (SpectralWeight.one.toCoeff q.val) hq n hnd
    rw [hphysical q.val q.property.1 q.property.2 hq n hnp,hfree] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hq (by positivity))
  have hD : D≤c/8 := by
    have hh : 192*(Real.exp (1/2))^2*B/Real.pi≤(n : ℝ) :=
      hNe.le.trans (by exact_mod_cast hne)
    have hh' := (div_le_iff₀ Real.pi_pos).mp hh
    dsimp only [D,c]
    nlinarith
  have hEpos : 0<E := by
    have hh := (abs_re_le_norm ((E : ℂ)-(c : ℂ)^2)).trans hd
    have hrw : ((E : ℂ)-(c : ℂ)^2).re=E-c^2 := by
      rw [←ofReal_pow,←ofReal_sub,ofReal_re]
    rw [hrw] at hh
    have hh' := (abs_le.mp hh).1
    have hc3 : 3<c := by dsimp only [c];nlinarith [Real.pi_gt_three]
    nlinarith
  have hroot : Complex.sqrt (E : ℂ)=(Real.sqrt E : ℂ) := by
    rw [Complex.sqrt_of_nonneg (by exact_mod_cast hEpos.le),ofReal_re]
  have hr : 0<Real.sqrt E := Real.sqrt_pos.mpr hEpos
  have hnear : |Real.sqrt E-c|≤1/8 := by
    have hh := norm_complexSqrt_sub_positive_le (E : ℂ) c D hc hd
    rw [hroot,←ofReal_sub,norm_real,Real.norm_eq_abs] at hh
    exact hh.trans ((div_le_iff₀ hc).mpr (by linarith))
  have hlo : (n : ℝ)≤Real.sqrt E := by
    have hh := (abs_le.mp hnear).1
    dsimp only [c] at hh
    nlinarith [Real.pi_gt_three]
  have hs : 32*‖SpectralWeight.one.toCoeff q.val‖≤Real.sqrt E := by
    have hh : 64*B≤(n : ℝ) := hNs.le.trans (by exact_mod_cast hns)
    nlinarith [mul_le_mul_of_nonneg_left hq (by norm_num : (0 : ℝ)≤32)]
  exact ⟨hroot,hr,hnear,hs,hlo⟩

end NLS.KdV
