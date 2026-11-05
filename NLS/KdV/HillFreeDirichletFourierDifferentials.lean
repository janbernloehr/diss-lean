import NLS.KdV.HillFreeGradientFourierCoefficients
import NLS.KdV.HillDirichletGardnerBrackets
import NLS.KdV.HillNativeCotangentExtension
import NLS.SequenceSpaces.OperatorBasisExt

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

include h0q h0r

/-- The exact ORIGINAL free Dirichlet-energy differential on every physical
native Hilbert direction. Every analytic root representative has the same
original mean and symmetric Fourier coefficients. -/
theorem hillDirichletBranch_free_fourier_fderiv
    (n : ℕ) (hn : 1 ≤ n) (a : Coeff 2 → ℂ)
    (ha : AnalyticAt ℂ a 0) (ha0 : a 0 = (freeHillValue n : ℂ))
    (hz : ∀ᶠ p in 𝓝 (0 : Coeff 2), hillL2DirichletCharacteristic p (a p) = 0)
    (h : Coeff 2) :
    (fderiv ℂ a 0) (hillNativeHilbertDirection h) = h 0-(h n+h (-(n : ℤ)))/2 := by
  let e := lp.evalCLM (𝕜 := ℂ) (fun _ : ℤ => ℂ) 2
  let R : Coeff 2 →L[ℂ] ℂ := e 0-(1/2 : ℂ) • (e n+e (-(n : ℤ)))
  have hA : AnalyticAt ℂ a (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)) := by
    simpa only [map_zero] using ha
  have hA0 : a (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)) =
      (hillDirichletEnergy 0 h0q h0r n hn : ℂ) := by
    rw [map_zero,ha0,hillDirichletEnergy_free h0q h0r n hn]
  have hZ : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)),
      hillL2DirichletCharacteristic p (a p) = 0 := by simpa only [map_zero] using hz
  have heq : (fderiv ℂ a 0).comp hillNativeHilbertDirection = R := by
    apply Coeff.continuousLinearMap_eq_of_single (by simp)
    intro j
    have hd := hillDirichletGradient_represents_branch (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential)
      n hn a hA hA0 hZ (lp.single 2 (2*j) 1)
    simp only [map_zero] at hd
    rw [←hillPhysicalDirectionPairing_apply,hillPhysicalDirectionPairing_single_unitFourier,
      unitFourierCoefficient_hillDirichletGradient_free h0q h0r] at hd
    change (fderiv ℂ a 0) (Coeff.insert (Coeff.parityEmbedding 0) (lp.single 2 j 1)) = _
    rw [Coeff.insert_single,Coeff.parityEmbedding_apply,add_zero,hd]
    change (if -j = 0 then (1 : ℂ) else 0) -
        ((if (n : ℤ) = -j then 1 else 0)+(if -(n : ℤ) = -j then 1 else 0))/2 =
      (lp.single 2 j 1 : Coeff 2) 0-(1/2 : ℂ)*
        ((lp.single 2 j 1 : Coeff 2) n+(lp.single 2 j 1 : Coeff 2) (-(n : ℤ)))
    have h1 : (n : ℤ) = -j ↔ j = -(n : ℤ) := by omega
    have h2 : -(n : ℤ) = -j ↔ j = (n : ℤ) := by omega
    simp only [neg_eq_zero,h1,h2,lp.single_apply,Pi.single_apply]
    split_ifs <;> first | omega | ring
  have hh := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L h) heq
  calc
    _ = R h := by simpa only [ContinuousLinearMap.comp_apply] using hh
    _ = _ := by
      change h 0-(1/2 : ℂ)*(h n+h (-(n : ℤ))) = _
      ring

end NLS.KdV
