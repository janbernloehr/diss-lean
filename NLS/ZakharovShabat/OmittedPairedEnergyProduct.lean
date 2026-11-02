import NLS.ZakharovShabat.PairedEnergyZeros
import NLS.ComplexAnalysis.RemovableFactorConvergence

/-! # Removing one positive energy factor

The filled entire product has the exact prefactor 2/(n*pi); this theorem
constructs the candidate product and does not identify a normalized differential.
-/
noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

def omittedPairedEnergyPartialProduct (rho : ℤ → ℂ) (n : ℕ+) (lambda : ℂ) (M : ℕ) : ℂ :=
  (2/((n : ℂ)*Real.pi))*∏ j ∈ (Finset.range M).erase ((n : ℕ)-1),
    ((rho ((j : ℤ)+1))^2-lambda)/((Real.pi : ℂ)*((j : ℂ)+1))^2

def omittedPairedEnergyProduct (rho : ℤ → ℂ) (n : ℕ+) (lambda : ℂ) : ℂ :=
  (2*(n : ℂ)*Real.pi)*dslope (pairedEnergyProduct rho) ((rho (n : ℤ))^2) lambda

theorem omittedPairedEnergyPartialProduct_factor (rho : ℤ → ℂ) (n : ℕ+)
    (lambda : ℂ) (M : ℕ) (hM : (n : ℕ) ≤ M) :
    (lambda-(rho (n : ℤ))^2)*omittedPairedEnergyPartialProduct rho n lambda M =
      (2*(n : ℂ)*Real.pi)*pairedEnergyPartialProduct rho lambda M := by
  let i := (n : ℕ)-1
  have hi : i+1 = (n : ℕ) := Nat.sub_add_cancel n.property
  have himem : i ∈ Finset.range M := Finset.mem_range.mpr (by dsimp only [i]; omega)
  have hidx : (i : ℤ)+1 = (n : ℤ) := by exact_mod_cast hi
  have hcast : (i : ℂ)+1 = (n : ℂ) := by exact_mod_cast hi
  let f : ℕ → ℂ := fun j => ((rho ((j : ℤ)+1))^2-lambda)/((Real.pi : ℂ)*((j : ℂ)+1))^2
  have hfi : f i = ((rho (n : ℤ))^2-lambda)/((n : ℂ)*Real.pi)^2 := by
    dsimp only [f]
    rw [hidx,hcast,mul_comm (Real.pi : ℂ)]
  have hprod := Finset.mul_prod_erase (Finset.range M) f himem
  change (lambda-(rho (n : ℤ))^2)*((2/((n : ℂ)*Real.pi))*∏ j ∈ (Finset.range M).erase i, f j) =
    (2*(n : ℂ)*Real.pi)*(-(∏ j ∈ Finset.range M, f j))
  rw [← hprod,hfi]
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
  have hp0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring

theorem analyticOnNhd_omittedPairedEnergyPartialProduct (rho : ℤ → ℂ) (n : ℕ+) (M : ℕ) :
    AnalyticOnNhd ℂ (fun z => omittedPairedEnergyPartialProduct rho n z M) univ := by
  intro z _
  exact analyticAt_const.mul (Finset.analyticAt_fun_prod _
    (fun j _ => (analyticAt_const.sub analyticAt_id).div_const))

variable {p : ENNReal} [Fact (1 ≤ p)]
variable (hp : p ≠ ⊤) (hp1 : 1 < p) (rho : ℤ → ℂ)
variable (hlp : Memℓp (fun j => rho j-(Real.pi : ℂ)*j) p)
variable (hzero : rho 0 = 0) (hneg : ∀ k : ℕ+, rho (-(k : ℤ)) = -rho (k : ℤ))
variable (hinj : Function.Injective rho)

include hp hlp hzero hneg in
theorem analyticOnNhd_omittedPairedEnergyProduct (n : ℕ+) :
    AnalyticOnNhd ℂ (omittedPairedEnergyProduct rho n) univ := by
  have hd := analyticOnNhd_dslope_of_analytic (pairedEnergyProduct rho) univ ((rho (n : ℤ))^2)
    (analyticOnNhd_pairedEnergyProduct hp rho hlp hzero hneg) (mem_univ _)
  intro z hz
  exact analyticAt_const.mul (hd z hz)

include hp hp1 hlp hzero hneg hinj in
theorem omittedPairedEnergyProduct_factor (n : ℕ+) (lambda : ℂ) :
    (lambda-(rho (n : ℤ))^2)*omittedPairedEnergyProduct rho n lambda =
      (2*(n : ℂ)*Real.pi)*pairedEnergyProduct rho lambda := by
  have hz := (pairedEnergyProduct_eq_zero_iff hp hp1 rho hlp hzero hneg hinj ((rho (n : ℤ))^2)).mpr ⟨n,rfl⟩
  have he := sub_smul_dslope (pairedEnergyProduct rho) ((rho (n : ℤ))^2) lambda
  simp only [smul_eq_mul,hz,sub_zero] at he
  dsimp only [omittedPairedEnergyProduct]
  linear_combination (2*(n : ℂ)*Real.pi)*he

include hp hp1 hlp hzero hneg hinj in
theorem tendstoLocallyUniformlyOn_omittedPairedEnergyProduct (n : ℕ+) :
    TendstoLocallyUniformlyOn (fun M z => omittedPairedEnergyPartialProduct rho n z M)
      (omittedPairedEnergyProduct rho n) atTop univ := by
  apply tendstoLocallyUniformlyOn_of_linear_factor _ _
    (fun M => differentiableOn_univ.mp (analyticOnNhd_omittedPairedEnergyPartialProduct rho n M).differentiableOn)
    (analyticOnNhd_omittedPairedEnergyProduct hp rho hlp hzero hneg n).continuous ((rho (n : ℤ))^2)
  let L : ℂ →L[ℂ] ℂ := (2*(n : ℂ)*Real.pi) • ContinuousLinearMap.id ℂ ℂ
  have hc := L.uniformContinuous.comp_tendstoLocallyUniformlyOn
    (tendstoLocallyUniformlyOn_pairedEnergyProduct hp rho hlp hzero hneg)
  have hc' : TendstoLocallyUniformlyOn
      (fun M z => (2*(n : ℂ)*Real.pi)*pairedEnergyPartialProduct rho z M)
      (fun z => (2*(n : ℂ)*Real.pi)*pairedEnergyProduct rho z) atTop univ := by
    simpa only [L,Function.comp_def,smul_apply,smul_eq_mul,ContinuousLinearMap.id_apply] using! hc
  have he : ∀ᶠ M : ℕ in atTop, ∀ z ∈ (univ : Set ℂ),
      Inseparable ((2*(n : ℂ)*Real.pi)*pairedEnergyPartialProduct rho z M)
        ((z-(rho (n : ℤ))^2)*omittedPairedEnergyPartialProduct rho n z M) := by
    filter_upwards [eventually_ge_atTop (n : ℕ)] with M hM z _
    exact Inseparable.of_eq (omittedPairedEnergyPartialProduct_factor rho n z M hM).symm
  exact (hc'.congr_inseparable he).congr_right
    (fun z _ => (omittedPairedEnergyProduct_factor hp hp1 rho hlp hzero hneg hinj n z).symm)

include hp hp1 hlp hzero hneg hinj in
theorem omittedPairedEnergyProduct_eq_zero_iff (n : ℕ+) (lambda : ℂ) :
    omittedPairedEnergyProduct rho n lambda = 0 ↔
      ∃ k : ℕ+, k ≠ n ∧ (rho (k : ℤ))^2 = lambda := by
  have hC : 2*(n : ℂ)*Real.pi ≠ 0 := mul_ne_zero
    (mul_ne_zero (by norm_num) (by exact_mod_cast n.ne_zero)) (by exact_mod_cast Real.pi_ne_zero)
  have hzn := (pairedEnergyProduct_eq_zero_iff hp hp1 rho hlp hzero hneg hinj ((rho (n : ℤ))^2)).mpr ⟨n,rfl⟩
  have hdn := pairedEnergyProduct_simple_zeros hp hp1 rho hlp hzero hneg hinj _ hzn
  have hBn : omittedPairedEnergyProduct rho n ((rho (n : ℤ))^2) ≠ 0 := by
    simpa only [omittedPairedEnergyProduct,dslope_same] using mul_ne_zero hC hdn
  constructor
  · intro hb
    have he : lambda ≠ (rho (n : ℤ))^2 := by intro he; subst lambda; exact hBn hb
    have hg : pairedEnergyProduct rho lambda = 0 := by
      have hf := omittedPairedEnergyProduct_factor hp hp1 rho hlp hzero hneg hinj n lambda
      rw [hb,mul_zero] at hf
      exact (mul_eq_zero.mp hf.symm).resolve_left hC
    obtain ⟨k,hk⟩ := (pairedEnergyProduct_eq_zero_iff hp hp1 rho hlp hzero hneg hinj lambda).mp hg
    exact ⟨k,fun h => he (h ▸ hk).symm,hk⟩
  · rintro ⟨k,hkn,hk⟩
    have he : lambda-(rho (n : ℤ))^2 ≠ 0 := by
      rw [← hk]
      exact sub_ne_zero.mpr ((pairedEnergyRoots_injective rho hneg hinj).ne hkn)
    have hg := (pairedEnergyProduct_eq_zero_iff hp hp1 rho hlp hzero hneg hinj lambda).mpr ⟨k,hk⟩
    have hf := omittedPairedEnergyProduct_factor hp hp1 rho hlp hzero hneg hinj n lambda
    rw [hg,mul_zero] at hf
    exact (mul_eq_zero.mp hf).resolve_left he

include hp hp1 hlp hzero hneg hinj in
theorem omittedPairedEnergyProduct_simple_zeros (n : ℕ+) (lambda : ℂ)
    (hb : omittedPairedEnergyProduct rho n lambda = 0) :
    deriv (omittedPairedEnergyProduct rho n) lambda ≠ 0 := by
  obtain ⟨k,_,hk⟩ := (omittedPairedEnergyProduct_eq_zero_iff hp hp1 rho hlp hzero hneg hinj n lambda).mp hb
  have hg := (pairedEnergyProduct_eq_zero_iff hp hp1 rho hlp hzero hneg hinj lambda).mpr ⟨k,hk⟩
  have hd := pairedEnergyProduct_simple_zeros hp hp1 rho hlp hzero hneg hinj lambda hg
  have hC : 2*(n : ℂ)*Real.pi ≠ 0 := mul_ne_zero
    (mul_ne_zero (by norm_num) (by exact_mod_cast n.ne_zero)) (by exact_mod_cast Real.pi_ne_zero)
  have hB := (analyticOnNhd_omittedPairedEnergyProduct hp rho hlp hzero hneg n lambda (mem_univ _)).differentiableAt.hasDerivAt
  have hleft := ((hasDerivAt_id lambda).sub_const ((rho (n : ℤ))^2)).mul hB
  have hright := ((analyticOnNhd_pairedEnergyProduct hp rho hlp hzero hneg lambda (mem_univ _)).differentiableAt.hasDerivAt).const_mul (2*(n : ℂ)*Real.pi)
  have he : (fun z : ℂ => (z-(rho (n : ℤ))^2)*omittedPairedEnergyProduct rho n z) =
      (fun z => (2*(n : ℂ)*Real.pi)*pairedEnergyProduct rho z) :=
    funext (omittedPairedEnergyProduct_factor hp hp1 rho hlp hzero hneg hinj n)
  change HasDerivAt (fun z : ℂ => (z-(rho (n : ℤ))^2)*omittedPairedEnergyProduct rho n z) _ lambda at hleft
  rw [he] at hleft
  have hdEq := hleft.unique hright
  rw [hb,mul_zero,zero_add] at hdEq
  intro hbad
  rw [hbad,mul_zero] at hdEq
  exact mul_ne_zero hC hd hdEq.symm

end NLS.ZakharovShabat
