import NLS.KdV.HillGlobalRegularCorrection
import NLS.KdV.HillOpenGapHalfLength
import NLS.KdV.HillDirichletAnalyticAngles

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- A physically matched primitive germ differs from the actual regular
correction only by its own-index linear angle term. -/
theorem eventually_hillPrimitive_eq_regularCorrection_of_terminal
    (n k : ℕ) (hn : 1≤n) (hk : 1≤k) (hgap : hillRealGapHalfLength q hq hr k≠0)
    (B ε : Coeff 2 → ℂ)
    (ht : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      cosineGapPoint (hillRealGapCenter p.val p.property.1 p.property.2 k)
        (hillRealGapHalfLength p.val p.property.1 p.property.2 k) (ε (SpectralWeight.one.toCoeff p.val))=
          (hillDirichletEnergy p.val p.property.1 p.property.2 k hk : ℂ) ∧
      Complex.sin (ε (SpectralWeight.one.toCoeff p.val))=hillDirichletGapSine p.val p.property.1 p.property.2 k hk ∧
      B (SpectralWeight.one.toCoeff p.val)=hillAbelianCosinePrimitive p.val p.property.1 p.property.2 n hn k
        (ε (SpectralWeight.one.toCoeff p.val))) :
    ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      B (SpectralWeight.one.toCoeff p.val)=hillRegularAbelianCorrection p.val p.property.1 p.property.2 n hn k hk+
        (if k=n then 1 else 0)*(ε (SpectralWeight.one.toCoeff p.val)-(Real.pi : ℂ)) := by
  have hg : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      hillRealGapHalfLength p.val p.property.1 p.property.2 k≠0 :=
    (continuous_hillRealGapHalfLength k).continuousAt.eventually_ne hgap
  filter_upwards [ht,hg] with p hp hgp
  let z := ε (SpectralWeight.one.toCoeff p.val)
  have hi : z.im=0 := hillDirichlet_angle_im_eq_zero p.val p.property.1 p.property.2 k hk hgp z hp.1 hp.2.1
  have he : z=(z.re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [ofReal_im] using hi
  have hpoint := hp.1
  have hsin := hp.2.1
  change cosineGapPoint _ _ z=_ at hpoint
  change Complex.sin z=_ at hsin
  rw [he] at hpoint hsin
  have hc := hillRegularAbelianCorrection_eq_of_terminal p.val p.property.1 p.property.2 n k hn hk hgp z.re hpoint hsin
  rw [hc,hp.2.2]
  change hillAbelianCosinePrimitive p.val p.property.1 p.property.2 n hn k z=
    (hillAbelianCosinePrimitive p.val p.property.1 p.property.2 n hn k (z.re : ℂ)-
      (if k=n then 1 else 0)*((z.re : ℂ)-(Real.pi : ℂ)))+
      (if k=n then 1 else 0)*(z-(Real.pi : ℂ))
  rw [he]
  simp only [ofReal_re]
  ring

end NLS.KdV
