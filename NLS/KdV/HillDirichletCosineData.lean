import NLS.KdV.HillDirichletGradientH1

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open MeasureTheory NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal

namespace NLS.KdV

def hillDirichletCosineCurve (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) : Curve (ℂ × ℂ) :=
  hillL2FrequencyStateCurve (SpectralWeight.one.toCoeff q.val)
    (Complex.sqrt (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)) (1,0)

theorem continuous_hillDirichletCosineCurve (n : ℕ) (hn : 1≤n) :
    Continuous (fun q : RealPeriodOneHillPotential => hillDirichletCosineCurve q n hn) := by
  have hm : Continuous (fun q : RealPeriodOneHillPotential =>
      (Complex.sqrt (hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ),SpectralWeight.one.toCoeff q.val)) :=
    (continuous_complex_sqrt_real.comp (continuous_hillDirichletEnergy n hn)).prodMk
      (SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val)
  convert! (continuous_hillL2FrequencyStateCurve_joint (1,0)).comp hm using 1

theorem hillDirichletEnergy_lt_of_lt
    (q : RealPeriodOneHillPotential) (n m : ℕ) (hn : 1≤n) (hm : 1≤m) (h : n<m) :
    hillDirichletEnergy q.val q.property.1 q.property.2 n hn<
      hillDirichletEnergy q.val q.property.1 q.property.2 m hm := by
  have hna := hillDirichletEnergy_mem_gap q.val q.property.1 q.property.2 n hn
  have hma := hillDirichletEnergy_mem_gap q.val q.property.1 q.property.2 m hm
  have hb := hillRealLabels_band_strict q.val q.property.1 q.property.2 n
  have hl := monotone_hillRealLabels q.val q.property.1 q.property.2 (show 2*n+1≤2*m-1 by omega)
  exact lt_of_le_of_lt hna.2 (lt_of_lt_of_le hb (le_trans hl hma.1))

theorem hillDirichletEnergy_ne_of_ne
    (q : RealPeriodOneHillPotential) (n m : ℕ) (hn : 1≤n) (hm : 1≤m) (h : n≠m) :
    (hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ)≠
      (hillDirichletEnergy q.val q.property.1 q.property.2 m hm : ℂ) := by
  intro he
  have he' := Complex.ofReal_injective he
  rcases lt_or_gt_of_ne h with hnm | hmn
  · exact (ne_of_lt (hillDirichletEnergy_lt_of_lt q n m hn hm hnm)) he'
  · exact (ne_of_gt (hillDirichletEnergy_lt_of_lt q m n hm hn hmn)) he'

end NLS.KdV
