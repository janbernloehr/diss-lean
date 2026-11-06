import NLS.KdV.HillFreeGradientFourierCoefficients
import NLS.KdV.HillHminusDirichletCotangent
import NLS.KdV.HillHminusLogNormingCotangent
import NLS.SequenceSpaces.WeightedFiniteCoefficients

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open scoped ENNReal
namespace NLS.KdV

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- ANY physically matched ORIGINAL free Dirichlet-energy H-minus-one germ
has the exact Fourier differential on EVERY complex H-minus-one direction. -/
theorem hillDirichletEnergy_hminus_free_fourier_fderiv
    (n : ℕ) (hn : 1 ≤ n) (a : PeriodOneHminusOne → ℂ) (ha : AnalyticAt ℂ a 0)
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential),
      a (hillOriginalHminusSource p.val) = (hillDirichletEnergy p.val p.property.1 p.property.2 n hn : ℂ))
    (h : PeriodOneHminusOne) :
    (fderiv ℂ a 0) h = h.val 0-(h.val n+h.val (-(n : ℤ)))/2 := by
  let e := WeightedCoeff.evalCLM (Weight.sobolev (-1)) 2
  let R : PeriodOneHminusOne →L[ℂ] ℂ := e 0-(1/2 : ℂ) • (e n+e (-(n : ℤ)))
  have hA : AnalyticAt ℂ a (hillOriginalHminusSource (0 : WeightedCoeff SpectralWeight.one.toWeight 2)) := by
    simpa only [map_zero] using ha
  have hg (j : ℤ) : (NLS.Poisson.hminusCotangentCLM (fderiv ℂ a 0)).val j =
      (if j = 0 then 1 else 0)-((if (n : ℤ) = j then 1 else 0)+(if -(n : ℤ) = j then 1 else 0))/2 := by
    have hh := hillDirichletEnergy_hminus_gradient_coefficients (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential)
      n hn a hA hmatch j
    simpa only [map_zero,NLS.Poisson.hminusScalarGradient] using
      hh.trans (unitFourierCoefficient_hillDirichletGradient_free h0q h0r n hn j)
  have heq : NLS.Poisson.hminusCotangentCLM (fderiv ℂ a 0) = NLS.Poisson.hminusCotangentCLM R := by
    apply Subtype.ext
    funext j
    rw [hg,NLS.Poisson.hminusCotangentCLM_apply]
    change (if j = 0 then (1 : ℂ) else 0)-
        ((if (n : ℤ) = j then 1 else 0)+(if -(n : ℤ) = j then 1 else 0))/2 =
      (WeightedCoeff.ofFinsupp (Weight.sobolev (-1)) 2 (Finsupp.single (-j) 1)).val 0 -
        (1/2 : ℂ)*((WeightedCoeff.ofFinsupp (Weight.sobolev (-1)) 2 (Finsupp.single (-j) 1)).val n+
          (WeightedCoeff.ofFinsupp (Weight.sobolev (-1)) 2 (Finsupp.single (-j) 1)).val (-(n : ℤ)))
    have h1 : -j = (n : ℤ) ↔ -(n : ℤ) = j := by omega
    have h2 : -j = -(n : ℤ) ↔ (n : ℤ) = j := by omega
    simp only [WeightedCoeff.ofFinsupp_apply,Finsupp.single_apply,neg_eq_zero,h1,h2]
    ring
  calc
    _ = R h := by
      rw [NLS.Poisson.hminusCotangentCLM_represents (fderiv ℂ a 0) h,heq]
      exact (NLS.Poisson.hminusCotangentCLM_represents R h).symm
    _ = _ := by
      change h.val 0-(1/2 : ℂ)*(h.val n+h.val (-(n : ℤ))) = _
      ring

/-- ANY physically matched ORIGINAL free logarithmic-norming H-minus-one
germ has the exact SIGNED Fourier differential on EVERY complex direction. -/
theorem hillLogNorming_hminus_free_fourier_fderiv
    (n : ℕ) (hn : 1 ≤ n) (k : PeriodOneHminusOne → ℂ) (hk : AnalyticAt ℂ k 0)
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential),
      k (hillOriginalHminusSource p.val) = (hillDirichletLogMultiplier p.val p.property.1 p.property.2 n hn : ℂ))
    (h : PeriodOneHminusOne) :
    (fderiv ℂ k 0) h = (h.val (-(n : ℤ))-h.val n)/(4*I*((n : ℂ)*Real.pi)) := by
  let e := WeightedCoeff.evalCLM (Weight.sobolev (-1)) 2
  let C : ℂ := (4*I*((n : ℂ)*Real.pi))⁻¹
  let R : PeriodOneHminusOne →L[ℂ] ℂ := C • (e (-(n : ℤ))-e n)
  have hK : AnalyticAt ℂ k (hillOriginalHminusSource (0 : WeightedCoeff SpectralWeight.one.toWeight 2)) := by
    simpa only [map_zero] using hk
  have hg (j : ℤ) : (NLS.Poisson.hminusCotangentCLM (fderiv ℂ k 0)).val j =
      ((if (n : ℤ) = j then 1 else 0)-(if -(n : ℤ) = j then 1 else 0))/(4*I*((n : ℂ)*Real.pi)) := by
    have hh := hillLogNorming_hminus_gradient_coefficients (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential)
      n hn k hK hmatch j
    simpa only [map_zero,NLS.Poisson.hminusScalarGradient] using
      hh.trans (unitFourierCoefficient_hillLogNormingGradient_free h0q h0r n hn j)
  have heq : NLS.Poisson.hminusCotangentCLM (fderiv ℂ k 0) = NLS.Poisson.hminusCotangentCLM R := by
    apply Subtype.ext
    funext j
    rw [hg,NLS.Poisson.hminusCotangentCLM_apply]
    change ((if (n : ℤ) = j then (1 : ℂ) else 0)-(if -(n : ℤ) = j then 1 else 0))/(4*I*((n : ℂ)*Real.pi)) =
      C*((WeightedCoeff.ofFinsupp (Weight.sobolev (-1)) 2 (Finsupp.single (-j) 1)).val (-(n : ℤ))-
        (WeightedCoeff.ofFinsupp (Weight.sobolev (-1)) 2 (Finsupp.single (-j) 1)).val n)
    have h1 : -j = (n : ℤ) ↔ -(n : ℤ) = j := by omega
    have h2 : -j = -(n : ℤ) ↔ (n : ℤ) = j := by omega
    simp only [WeightedCoeff.ofFinsupp_apply,Finsupp.single_apply,h1,h2]
    dsimp only [C]
    ring
  calc
    _ = R h := by
      rw [NLS.Poisson.hminusCotangentCLM_represents (fderiv ℂ k 0) h,heq]
      exact (NLS.Poisson.hminusCotangentCLM_represents R h).symm
    _ = _ := by
      change C*(h.val (-(n : ℤ))-h.val n) = _
      dsimp only [C]
      ring

/-- Genuine ORIGINAL free Dirichlet and norming germs with their complete
Fourier differentials. All analyticity and physical matching are constructed. -/
theorem exists_hillFreeDirichletNorming_hminus_fourier_germs (n : ℕ) (hn : 1 ≤ n) :
    ∃ a k : PeriodOneHminusOne → ℂ,
      AnalyticAt ℂ a 0 ∧ AnalyticAt ℂ k 0 ∧ a 0 = (freeHillValue n : ℂ) ∧ k 0 = 0 ∧
      (∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential),
        a (hillOriginalHminusSource p.val) = (hillDirichletEnergy p.val p.property.1 p.property.2 n hn : ℂ) ∧
        k (hillOriginalHminusSource p.val) = (hillDirichletLogMultiplier p.val p.property.1 p.property.2 n hn : ℂ)) ∧
      ∀ h : PeriodOneHminusOne,
        (fderiv ℂ a 0) h = h.val 0-(h.val n+h.val (-(n : ℤ)))/2 ∧
        (fderiv ℂ k 0) h = (h.val (-(n : ℤ))-h.val n)/(4*I*((n : ℂ)*Real.pi)) := by
  obtain ⟨a,T,k,ha,_,hk,ha0,_,hk0,_,hM⟩ :=
    exists_hillDirichlet_norming_hminus_analytic_extension (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential) n hn
  have hA : AnalyticAt ℂ a 0 := by simpa only [map_zero] using ha
  have hK : AnalyticAt ℂ k 0 := by simpa only [map_zero] using hk
  have hA0 : a 0 = (freeHillValue n : ℂ) := by
    simpa only [map_zero,hillDirichletEnergy_free h0q h0r n hn] using ha0
  have hK0 : k 0 = 0 := by
    simpa only [map_zero,hillDirichletLogMultiplier_zero_potential h0q h0r n hn,ofReal_zero] using hk0
  have hAM := hM.mono (fun _ hp => hp.1)
  have hKM := hM.mono (fun _ hp => hp.2.2)
  refine ⟨a,k,hA,hK,hA0,hK0,?_,?_⟩
  · exact hAM.and hKM
  · intro h
    exact ⟨hillDirichletEnergy_hminus_free_fourier_fderiv h0q h0r n hn a hA hAM h,
      hillLogNorming_hminus_free_fourier_fderiv h0q h0r n hn k hK hKM h⟩

end NLS.KdV
