import NLS.ZakharovShabat.SourceGapInterpolationProduct
import NLS.ComplexAnalysis.OddSquareDescent
import NLS.ComplexAnalysis.SquareProductConvergence

/-! # Positive energy products of paired frequency roots

Pairing the literal signed cutoffs fixes the minus sign and every pi-squared
normalization. The entire energy limit includes the ramification point zero.
-/
noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

def pairedEnergyPartialProduct (rho : ℤ → ℂ) (lambda : ℂ) (M : ℕ) : ℂ :=
  -∏ j ∈ Finset.range M, ((rho ((j : ℤ)+1))^2-lambda)/((Real.pi : ℂ)*((j : ℂ)+1))^2

def pairedEnergyProduct (rho : ℤ → ℂ) : ℂ → ℂ :=
  oddSquareDescent (entireSingleSpectralProduct rho)

theorem signedPartialProduct_eq_pairedEnergy (rho : ℤ → ℂ)
    (hzero : rho 0 = 0) (hneg : ∀ k : ℕ+, rho (-(k : ℤ)) = -rho (k : ℤ))
    (z : ℂ) (M : ℕ) :
    singleSpectralPartialProduct rho z M = (2*z)*pairedEnergyPartialProduct rho (z^2) M := by
  rw [singleSpectralPartialProduct,prod_symmetric_interval]
  have hp (j : ℕ) :
      singleSpectralFactor rho z ((j : ℤ)+1)*singleSpectralFactor rho z (-((j : ℤ)+1)) =
      ((rho ((j : ℤ)+1))^2-z^2)/((Real.pi : ℂ)*((j : ℂ)+1))^2 := by
    have hn : rho (-((j : ℤ)+1)) = -rho ((j : ℤ)+1) := by
      simpa only [Nat.cast_add,Nat.cast_one] using! hneg (⟨j+1,by omega⟩ : ℕ+)
    simp only [singleSpectralFactor,singleSpectralDenominator,
      if_neg (by omega : (j : ℤ)+1 ≠ 0),if_neg (by omega : -((j : ℤ)+1) ≠ 0),hn,
      Int.cast_add,Int.cast_one,Int.cast_natCast,Int.cast_neg,mul_neg]
    have ha : (Real.pi : ℂ)*((j : ℂ)+1) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) (Nat.cast_add_one_ne_zero j)
    field_simp
    ring
  simp only [hp]
  simp only [singleSpectralFactor,singleSpectralDenominator,hzero,ite_true,zero_sub,div_one]
  dsimp only [pairedEnergyPartialProduct]
  ring

theorem analyticOnNhd_pairedEnergyPartialProduct (rho : ℤ → ℂ) (M : ℕ) :
    AnalyticOnNhd ℂ (fun z => pairedEnergyPartialProduct rho z M) univ := by
  intro z _
  exact (Finset.analyticAt_fun_prod _
    (fun j _ => (analyticAt_const.sub analyticAt_id).div_const)).neg

theorem entireSingleSpectralProduct_odd_of_paired {p : ENNReal} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (rho : ℤ → ℂ) (hlp : Memℓp (fun j => rho j-(Real.pi : ℂ)*j) p)
    (hzero : rho 0 = 0) (hneg : ∀ k : ℕ+, rho (-(k : ℤ)) = -rho (k : ℤ)) (z : ℂ) :
    entireSingleSpectralProduct rho (-z) = -entireSingleSpectralProduct rho z := by
  have h := tendstoLocallyUniformlyOn_entireSingleSpectralProduct hp rho hlp
  have he (M : ℕ) : singleSpectralPartialProduct rho (-z) M = -singleSpectralPartialProduct rho z M := by
    rw [signedPartialProduct_eq_pairedEnergy rho hzero hneg,
      signedPartialProduct_eq_pairedEnergy rho hzero hneg,neg_sq]
    ring
  exact tendsto_nhds_unique (h.tendsto_at (mem_univ (-z)))
    (by simpa only [he] using (h.tendsto_at (mem_univ z)).neg)

theorem pairedEnergyProduct_factor {p : ENNReal} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (rho : ℤ → ℂ) (hlp : Memℓp (fun j => rho j-(Real.pi : ℂ)*j) p)
    (hzero : rho 0 = 0) (hneg : ∀ k : ℕ+, rho (-(k : ℤ)) = -rho (k : ℤ)) (z : ℂ) :
    (2*z)*pairedEnergyProduct rho (z^2) = entireSingleSpectralProduct rho z :=
  oddSquareDescent_factor _ (entireSingleSpectralProduct_odd_of_paired hp rho hlp hzero hneg) z

theorem analyticOnNhd_pairedEnergyProduct {p : ENNReal} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (rho : ℤ → ℂ) (hlp : Memℓp (fun j => rho j-(Real.pi : ℂ)*j) p)
    (hzero : rho 0 = 0) (hneg : ∀ k : ℕ+, rho (-(k : ℤ)) = -rho (k : ℤ)) :
    AnalyticOnNhd ℂ (pairedEnergyProduct rho) univ :=
  analyticOnNhd_oddSquareDescent _ (analyticOnNhd_entireSingleSpectralProduct hp rho hlp)
    (entireSingleSpectralProduct_odd_of_paired hp rho hlp hzero hneg)

theorem tendstoLocallyUniformlyOn_pairedEnergyProduct {p : ENNReal} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (rho : ℤ → ℂ) (hlp : Memℓp (fun j => rho j-(Real.pi : ℂ)*j) p)
    (hzero : rho 0 = 0) (hneg : ∀ k : ℕ+, rho (-(k : ℤ)) = -rho (k : ℤ)) :
    TendstoLocallyUniformlyOn (fun M z => pairedEnergyPartialProduct rho z M)
      (pairedEnergyProduct rho) atTop univ := by
  apply tendstoLocallyUniformlyOn_of_square_pullback _ _
    (fun M => differentiableOn_univ.mp (analyticOnNhd_pairedEnergyPartialProduct rho M).differentiableOn)
    (analyticOnNhd_pairedEnergyProduct hp rho hlp hzero hneg).continuous
  simpa only [pairedEnergyProduct_factor hp rho hlp hzero hneg,
    ← signedPartialProduct_eq_pairedEnergy rho hzero hneg] using
    tendstoLocallyUniformlyOn_entireSingleSpectralProduct hp rho hlp

end NLS.ZakharovShabat
