import NLS.KdV.HillFreeOwnPeriodProduct
import NLS.KdV.HillBoundedOwnPeriodError
import NLS.ComplexAnalysis.BanachAnalyticZeroBound

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- A common local displacement bound for the actual free own periods
at every bounded Hilbert root vector. -/
theorem norm_hillFreeOwnHilbertPeriod_shift_le
    (n : ℕ) (hn : 1≤n) (a h : Coeff 2) (R : ℝ) (ha : ‖a‖≤R) (hh : ‖h‖<1/4) :
    ‖hillAbelianHilbertPeriod 0 h0q h0r n n (a+h)-hillAbelianHilbertPeriod 0 h0q h0r n n a‖≤
      (16*Real.exp ((2/Real.pi^2)*(R+1)))*‖h‖ := by
  let f : Coeff 2 → ℂ := fun v => hilbertWeightedProduct (hillFreeSeparatedWeight n n) (a+v)-
    hilbertWeightedProduct (hillFreeSeparatedWeight n n) a
  let M := 2*Real.exp ((2/Real.pi^2)*(R+1))
  have hf : AnalyticOnNhd ℂ f (ball 0 1) := by
    intro v _
    exact ((analyticOnNhd_hilbertWeightedProduct _ _ (mem_univ _)).comp
      (f := fun v : Coeff 2 => a+v) (analyticAt_const.add analyticAt_id)).sub analyticAt_const
  have hf0 : f 0=0 := by simp only [f,add_zero,sub_self]
  have hb (v : Coeff 2) (hv : v∈ball 0 1) : ‖f v‖≤M := by
    have hv1 : ‖v‖<1 := by simpa only [mem_ball,dist_zero_right] using hv
    have hav : ‖a+v‖≤R+1 := (norm_add_le _ _).trans (by linarith)
    have hp1 : ‖hilbertWeightedProduct (hillFreeSeparatedWeight n n) (a+v)‖≤Real.exp ((2/Real.pi^2)*(R+1)) :=
      (norm_hilbertWeightedProduct_hillSeparated_le n n (a+v)).trans (Real.exp_le_exp.mpr (by gcongr))
    have hp0 : ‖hilbertWeightedProduct (hillFreeSeparatedWeight n n) a‖≤Real.exp ((2/Real.pi^2)*(R+1)) :=
      (norm_hilbertWeightedProduct_hillSeparated_le n n a).trans (Real.exp_le_exp.mpr (by gcongr;linarith))
    exact (norm_sub_le _ _).trans (by dsimp only [M];linarith)
  have hbound := norm_le_mul_norm_of_analytic_zero_ball_bound f 1 M (by norm_num) hf hf0 hb h
    (by simpa only [mem_ball,dist_zero_right] using hh)
  rw [hillFreeOwnHilbertPeriod_eq_product h0q h0r n hn (a+h),hillFreeOwnHilbertPeriod_eq_product h0q h0r n hn a]
  convert! hbound using 1
  dsimp only [M]
  ring

/-- All high own periods are uniformly close to one for bounded
potentials and roots in one fixed neighborhood of a compact root set. -/
theorem exists_hillAbelianComplexOwnPeriod_uniform_high_near_compact
    (K : Set (Coeff 2)) (hK : IsCompact K) (B A : ℝ) (hB : 0≤B) :
    ∃ J : ℕ, ∃ η : ℝ, 1≤J ∧ 0<η ∧ ∀ n : ℕ, J≤n → ∀ a0∈K,
      ∀ a p : Coeff 2, ‖a‖≤A → ‖p‖≤B → ‖a-a0‖<η →
        ‖hillAbelianComplexPeriod 0 h0q h0r n n (a,p)-1‖<1/2 := by
  obtain ⟨R,hR,hRbound⟩ := hK.isBounded.exists_pos_norm_le
  let L := 16*Real.exp ((2/Real.pi^2)*(R+1))
  have hL : 0<L := by dsimp only [L];positivity
  let η := min (1/4) (1/(8*L))
  have hη : 0<η := by dsimp only [η];positivity
  obtain ⟨J0,hJ0⟩ := exists_hillFreeOwnHilbertPeriod_uniform_on_compact h0q h0r K hK (1/8) (by norm_num)
  obtain ⟨J1,C,hJ1,hC,hErr⟩ := exists_hillAbelianComplexOwnPeriod_bounded_tail_error h0q h0r B
  let M := C*Real.exp ((8/Real.pi^2)*A)*B
  have hM : 0≤M := by dsimp only [M];positivity
  have ht : Tendsto (fun n : ℕ => M/(n : ℝ)) atTop (𝓝 0) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).const_div_atTop M
  obtain ⟨J2,hJ2⟩ := Metric.tendsto_atTop.mp ht (1/8) (by norm_num)
  let J := max J1 (max J0 J2)
  refine ⟨J,η,hJ1.trans (le_max_left _ _),hη,?_⟩
  intro n hn a0 ha0 a p ha hp hshift
  have hn1 : 1≤n := hJ1.trans ((le_max_left J1 (max J0 J2)).trans hn)
  have hcomplex : ‖hillAbelianComplexPeriod 0 h0q h0r n n (a,p)-hillAbelianHilbertPeriod 0 h0q h0r n n a‖<1/8 := by
    have he := hErr p hp n ((le_max_left _ _).trans hn) a
    have hbd : C*Real.exp ((8/Real.pi^2)*‖a‖)*‖p‖/(n : ℝ)≤M/(n : ℝ) := by dsimp only [M];gcongr
    have hsmall : M/(n : ℝ)<1/8 := by
      have hh := hJ2 n (((le_max_right _ _).trans (le_max_right _ _)).trans hn)
      simpa only [dist_zero_right,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤M/(n : ℝ))] using hh
    exact (he.trans hbd).trans_lt hsmall
  have hfree : ‖hillAbelianHilbertPeriod 0 h0q h0r n n a-hillAbelianHilbertPeriod 0 h0q h0r n n a0‖<1/8 := by
    have hh : ‖a-a0‖<1/4 := hshift.trans_le (min_le_left _ _)
    have hbd := norm_hillFreeOwnHilbertPeriod_shift_le h0q h0r n hn1 a0 (a-a0) R (hRbound _ ha0) hh
    have hrestore : a0+(a-a0)=a := by abel
    rw [hrestore] at hbd
    have hsmall : L*‖a-a0‖<1/8 := by
      have hh' : ‖a-a0‖<1/(8*L) := hshift.trans_le (min_le_right _ _)
      have hh'' := (lt_div_iff₀ (by positivity : 0<8*L)).mp hh'
      nlinarith
    exact hbd.trans_lt hsmall
  have hbase : ‖hillAbelianHilbertPeriod 0 h0q h0r n n a0-1‖<1/8 :=
    hJ0 n hn1 (((le_max_left _ _).trans (le_max_right _ _)).trans hn) a0 ha0
  have he : hillAbelianComplexPeriod 0 h0q h0r n n (a,p)-1=
      (hillAbelianComplexPeriod 0 h0q h0r n n (a,p)-hillAbelianHilbertPeriod 0 h0q h0r n n a)+
      (hillAbelianHilbertPeriod 0 h0q h0r n n a-hillAbelianHilbertPeriod 0 h0q h0r n n a0)+
      (hillAbelianHilbertPeriod 0 h0q h0r n n a0-1) := by ring
  rw [he]
  exact norm_add₃_le.trans_lt (by linarith)

end NLS.KdV
