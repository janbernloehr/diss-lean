import NLS.KdV.HillFreeHminusFourierDifferentials
import NLS.KdV.HillHminusOriginalDirichletSheetGerm
import NLS.KdV.HillHminusPhysicalGermDifferentials
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.KdV

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- ANY physically matched ORIGINAL free Dirichlet sheet germ has the
complete signed Fourier differential, including every positive closed gap. -/
theorem hillDirichletSheet_hminus_free_fourier_fderiv
    (n : ℕ) (hn : 1 ≤ n) (S : PeriodOneHminusOne → ℂ) (hS : AnalyticAt ℂ S 0)
    (hSM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential),
      S (hillOriginalHminusSource p.val) = hillDirichletSheetRoot
        (SpectralWeight.one.toCoeff p.val) (hillDirichletEnergy p.val p.property.1 p.property.2 n hn))
    (h : PeriodOneHminusOne) :
    (fderiv ℂ S 0) h = (-1 : ℂ)^n*(h.val (-(n : ℤ))-h.val n)/(2*I*((n : ℂ)*Real.pi)) := by
  obtain ⟨a,k,_,hk,_,hk0,hM,hD⟩ := exists_hillFreeDirichletNorming_hminus_fourier_germs h0q h0r n hn
  let c : ℂ := (-1)^n*2
  let R : PeriodOneHminusOne → ℂ := fun p => c*Complex.sinh (k p)
  have hR : AnalyticAt ℂ R 0 := analyticAt_const.mul (Complex.analyticAt_sinh.comp (f := k) hk)
  have hRM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential),
      R (hillOriginalHminusSource p.val) = hillDirichletSheetRoot
        (SpectralWeight.one.toCoeff p.val) (hillDirichletEnergy p.val p.property.1 p.property.2 n hn) := by
    filter_upwards [hM] with p hp
    dsimp only [R,c]
    rw [hp.2]
    symm
    simpa only [ofReal_mul,ofReal_pow,ofReal_neg,ofReal_one,ofReal_ofNat,Complex.ofReal_sinh] using
      hillDirichletSheetRoot_at_dirichlet_eq_norming p.val p.property.1 p.property.2 n hn
  have hEq := hillHminusPhysicalGerm_fderiv_eq_of_eventuallyEq
    (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential) S R
    (by simpa only [map_zero] using hS) (by simpa only [map_zero] using hR)
    (by filter_upwards [hSM,hRM] with p hp hpr; exact hp.trans hpr.symm)
  have hEq0 : fderiv ℂ S 0 = fderiv ℂ R 0 := by simpa only [map_zero] using hEq
  have hDR := hk.differentiableAt.hasFDerivAt.csinh.const_smul c
  simp only [hk0,Complex.cosh_zero,one_smul] at hDR
  have hRD : fderiv ℂ R 0 = c • fderiv ℂ k 0 := hDR.fderiv
  rw [hEq0,hRD,smul_apply,smul_eq_mul,(hD h).2]
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  dsimp only [c]
  field_simp [hn0,Real.pi_ne_zero,I_ne_zero]
  ring

/-- Genuine ORIGINAL free sheet and Dirichlet germs retain the actual
complex radicand identity and the proved signed Fourier sheet differential. -/
theorem exists_hillFreeDirichletSheet_hminus_fourier_germ (n : ℕ+) :
    ∃ a S : PeriodOneHminusOne → ℂ,
      AnalyticAt ℂ a 0 ∧ AnalyticAt ℂ S 0 ∧ a 0 = (freeHillValue n : ℂ) ∧
      (∀ᶠ b in 𝓝 (0 : PeriodOneHminusOne), S b^2 = hillHminusRadicand b (a b)) ∧
      (∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential),
        a (hillOriginalHminusSource p.val) = (hillDirichletEnergy p.val p.property.1 p.property.2 n n.pos : ℂ) ∧
        S (hillOriginalHminusSource p.val) = hillDirichletSheetRoot
          (SpectralWeight.one.toCoeff p.val) (hillDirichletEnergy p.val p.property.1 p.property.2 n n.pos)) ∧
      ∀ h : PeriodOneHminusOne,
        (fderiv ℂ S 0) h = (-1 : ℂ)^(n : ℕ)*(h.val (-(n : ℤ))-h.val n)/(2*I*((n : ℂ)*Real.pi)) := by
  obtain ⟨a,S,ha,hS,ha0,hC,hM⟩ := exists_hillOriginal_dirichlet_sheet_hminus_physical_germ
    (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential) n
  have hA : AnalyticAt ℂ a 0 := by simpa only [map_zero] using ha
  have hSA : AnalyticAt ℂ S 0 := by simpa only [map_zero] using hS
  have hA0 : a 0 = (freeHillValue n : ℂ) := by
    simpa only [map_zero,hillDirichletEnergy_free h0q h0r n n.pos] using ha0
  have hC0 : ∀ᶠ b in 𝓝 (0 : PeriodOneHminusOne), S b^2 = hillHminusRadicand b (a b) := by
    simpa only [map_zero] using hC
  exact ⟨a,S,hA,hSA,hA0,hC0,hM,
    hillDirichletSheet_hminus_free_fourier_fderiv h0q h0r n n.pos S hSA (hM.mono (fun _ hp => hp.2))⟩

end NLS.KdV
