import NLS.MKdV.SobolevMiuraPotential
import NLS.Fourier.UnitIntervalL2Equiv
import NLS.SequenceSpaces.PeriodOneMiuraShift

/-! # Literal physical L2 classes of H1 Miura profiles and images

The unit Fourier isometry realizes the original H1 coefficients by their
actual periodic representative. Its Miura image is the class of u'+u²,
with exactly the unit-period derivative symbol and constant shift.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open NLS.Fourier NLS.ZakharovShabat
namespace NLS.MKdV

theorem unitL2Synthesis_scalarInclusion_representative (a : ScalarDomain 2) :
    unitL2SynthesisEquiv (scalarInclusion a) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      (fun s : ℝ => periodOneSobolevSynthesis a (s : AddCircle (2 : ℝ))) := by
  let f : ℝ → ℂ := fun s => periodOneSobolevSynthesis a (s : AddCircle (2 : ℝ))
  have hf := memLp_two_interval (continuous_periodOneSobolevSynthesis a) 0 1 (by norm_num)
  have he : unitIntervalMemLpCoefficients f hf = scalarInclusion a := by
    ext k
    rw [unitIntervalMemLpCoefficients_apply,intervalFourierCoefficient_eq_fourierCoeffOn (by norm_num)]
    simpa only [periodOneCoefficient,f,scalarInclusion_apply] using
      periodOneCoefficient_periodOneSobolevSynthesis a k
  rw [← he,unitL2SynthesisEquiv_memLpCoefficients]
  exact hf.coeFn_toLp

theorem unitL2Synthesis_sobolevMiura_representative (a : ScalarDomain 2) :
    unitL2SynthesisEquiv (sobolevMiuraUnitPotential a) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      miuraPotential (fun s : ℝ => periodOneSobolevSynthesis a (s : AddCircle (2 : ℝ))) := by
  let f : ℝ → ℂ := fun s => periodOneSobolevSynthesis a (s : AddCircle (2 : ℝ))
  have hf : MemLp (miuraPotential f) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (memLp_deriv_periodOneSobolevSynthesis a).add
      (memLp_two_interval ((continuous_periodOneSobolevSynthesis a).pow 2) 0 1 (by norm_num))
  have he : unitIntervalMemLpCoefficients (miuraPotential f) hf = sobolevMiuraUnitPotential a := by
    ext k
    rw [unitIntervalMemLpCoefficients_apply,intervalFourierCoefficient_eq_fourierCoeffOn (by norm_num)]
    exact (sobolevMiuraUnitPotential_physical a k).symm
  rw [← he,unitL2SynthesisEquiv_memLpCoefficients]
  exact hf.coeFn_toLp

theorem unitL2Synthesis_single_zero_representative (c : ℂ) :
    unitL2SynthesisEquiv (lp.single 2 0 c) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] fun _ => c := by
  have h := unitL2Synthesis_scalarInclusion_representative (scalarMode 0 c)
  simpa only [scalarInclusion_scalarMode,periodOneSobolevSynthesis_scalarMode,mul_zero,
    wave_zero,mul_one] using h

/-- An L2 Fourier Miura image identifies the actual physical potential
and forces precisely the H1 regularity needed by integration by parts. -/
theorem exists_physical_H1_Miura_lift (u q : Coeff 2) (c : ℂ)
    (himage : periodOneMiura u = periodOneL2Inclusion (q+lp.single 2 0 c)) :
    ∃ a : ScalarDomain 2, scalarInclusion a = u ∧
      unitL2SynthesisEquiv u =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
        (fun s : ℝ => periodOneSobolevSynthesis a (s : AddCircle (2 : ℝ))) ∧
      (fun s : ℝ => miuraPotential (fun t => periodOneSobolevSynthesis a (t : AddCircle (2 : ℝ))) s-c)
        =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] unitL2SynthesisEquiv q := by
  let a : ScalarDomain 2 := ⟨u,periodOneMiura_memlp_sobolev_one u _ himage⟩
  have ha : scalarInclusion a = u := by ext k; exact scalarInclusion_apply a k
  have hp : sobolevMiuraUnitPotential a = q+lp.single 2 0 c := by
    ext k
    have h := congrArg (fun p : PeriodOneHminusOne => p.val k) himage
    rw [periodOneMiura_apply,periodOneL2Inclusion_apply] at h
    rw [sobolevMiuraUnitPotential_apply]
    exact h
  refine ⟨a,ha,?_,?_⟩
  · rw [← ha]
    exact unitL2Synthesis_scalarInclusion_representative a
  · have hphys := unitL2Synthesis_sobolevMiura_representative a
    rw [hp,map_add] at hphys
    filter_upwards [hphys,Lp.coeFn_add (unitL2SynthesisEquiv q) (unitL2SynthesisEquiv (lp.single 2 0 c)),
      unitL2Synthesis_single_zero_representative c] with s hs hadd hc
    rw [hadd,Pi.add_apply,hc] at hs
    exact sub_eq_iff_eq_add.mpr hs.symm

end NLS.MKdV
