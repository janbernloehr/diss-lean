import NLS.MKdV.QuasiHillL2Energy

/-! The affine-energy source has its literal physical L2 representative.
No continuity of the Miura lift or endpoint trace is assumed. -/
noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.ZakharovShabat
namespace NLS.MKdV

/-- The original zero Fourier mode is the physical constant on the unit interval. -/
theorem unitL2Synthesis_single_zero (c : ℂ) :
    unitL2SynthesisEquiv (lp.single 2 0 c) =ᵐ[volume.restrict (Ioc (0:ℝ) 1)] (fun _ => c) := by
  have he : Coeff.ofFinsupp (p := 2) (Finsupp.single 0 c) = lp.single 2 0 c := by
    ext n
    by_cases hn : n = 0 <;> simp [Coeff.ofFinsupp_apply,lp.single_apply,hn]
  have h := unitL2SynthesisEquiv_ofFinsupp (Finsupp.single 0 c)
  rw [he] at h
  have hp : polynomial (Finsupp.single 0 c) = (fun _ : ℝ => c) := by
    funext x
    simp [polynomial,Finsupp.sum_single_index,wave]
  exact h.trans (Filter.EventuallyEq.of_eq hp)

/-- Actual physical coefficient equality for every complex L2 lift and
every energy, using the original unit-period Fourier synthesis. -/
theorem quasiHillEnergySource_representative (u : Coeff 2) (lambda : ℂ) :
    intervalL2Representative (sourcePhysicalL2 (quasiHillEnergySource u lambda))
      =ᵐ[volume.restrict (Ioc (0:ℝ) 1)]
      (fun x => (-I*(unitL2SynthesisEquiv u) x+(lambda-1)/2,
        I*(unitL2SynthesisEquiv u) x+(lambda-1)/2)) := by
  let c := (lambda-1)/2
  have hf : (quasiHillEnergySource u lambda).fst = (-I) • u+lp.single 2 0 c := by
    change ((-I) • u+lp.single 2 0 c)+0 = _
    exact add_zero _
  have hg : (quasiHillEnergySource u lambda).snd = I • u+lp.single 2 0 c := by
    change 0+(I • u+lp.single 2 0 c) = _
    exact zero_add _
  rw [← sourcePhysicalL2Equiv_apply]
  change (fun x => (unitL2SynthesisEquiv (quasiHillEnergySource u lambda).fst x,
    unitL2SynthesisEquiv (quasiHillEnergySource u lambda).snd x)) =ᵐ[_] _
  rw [hf,hg,map_add,map_add,map_smul,map_smul]
  filter_upwards [unitL2Synthesis_single_zero c,
    Lp.coeFn_add ((-I) • unitL2SynthesisEquiv u) (unitL2SynthesisEquiv (lp.single 2 0 c)),
    Lp.coeFn_add (I • unitL2SynthesisEquiv u) (unitL2SynthesisEquiv (lp.single 2 0 c)),
    Lp.coeFn_smul (-I) (unitL2SynthesisEquiv u),Lp.coeFn_smul I (unitL2SynthesisEquiv u)]
      with x hc hleft hright hsmleft hsmright
  simp only [hleft,hright,Pi.add_apply,hsmleft,hsmright,Pi.smul_apply,hc,smul_eq_mul]
  rfl

end NLS.MKdV
