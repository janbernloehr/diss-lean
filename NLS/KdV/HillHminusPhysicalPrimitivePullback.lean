import NLS.KdV.HillHminusOneMiuraSheets
import NLS.KdV.HillHminusPsiCharts
import NLS.ZakharovShabat.SourceFullAbelianPrimitive

/-! # The literal physical primitive under a shifted Miura chart -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.KdV.HillHminusPsiChart

/-- Both physical logarithm normalizations agree off the real axis.
The energy translation is the chart's actual squared shift. -/
theorem physical_primitive_squared_frequency (P : HillHminusPsiChart)
    (q : RealPeriodOneHillPotential) (hq : hillOriginalHminusSource q.val ∈ P.source)
    (hr : ∀ j : ℤ, P.miura.lift (hillOriginalHminusSource q.val) (-j) =
      conj (P.miura.lift (hillOriginalHminusSource q.val) j))
    (c : ℝ) (hshift : P.miura.energyShift = (c : ℂ)^2)
    (z : ℂ) (hzr : 0 < z.re) (hzi : z.im ≠ 0) :
    hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q.val) (z^2-P.miura.energyShift) =
      sourceAbelianPrimitive (by simp) (by norm_num)
        (hillMiuraDiagonal (P.miura.lift (hillOriginalHminusSource q.val)))
        (hillMiuraRealSource (⟨P.miura.lift (hillOriginalHminusSource q.val),hr⟩ : PeriodOneRealL2)).property z := by
  let u : PeriodOneRealL2 := ⟨P.miura.lift (hillOriginalHminusSource q.val),hr⟩
  have hi : (z^2-P.miura.energyShift).im ≠ 0 := by
    rw [hshift, ← ofReal_pow]
    simp only [sub_im,ofReal_im,sub_zero,pow_two,mul_im]
    intro he
    apply mul_ne_zero (ne_of_gt hzr) hzi
    nlinarith
  have himage : periodOneMiura u.val = hillOriginalHminusSource q.val +
      periodOneL2Inclusion (lp.single 2 0 ((c^2 : ℝ) : ℂ)) := by
    simpa only [ofReal_pow, ← hshift] using P.miura.image _ hq.1
  have he := (hillHminus_shifted_miura_sheets u (hillOriginalHminusSource q.val) (c^2)
    himage z hzr hzi).2
  rw [ofReal_pow, ← hshift,
    hillHminusContinuedPrimitive_original_source_agreement q.val q.property.1 _
      (mem_hillL2ContinuationDomain_of_im_ne_zero q.val q.property.1 q.property.2 _ hi)] at he
  simpa only [hillL2RealCutPrimitive,if_neg hi,hillMiuraRealSource,u] using! he

theorem full_primitive_squared_frequency (P : HillHminusPsiChart)
    (q : RealPeriodOneHillPotential) (hq : hillOriginalHminusSource q.val ∈ P.source)
    (hr : ∀ j : ℤ, P.miura.lift (hillOriginalHminusSource q.val) (-j) =
      conj (P.miura.lift (hillOriginalHminusSource q.val) j))
    (c : ℝ) (hshift : P.miura.energyShift = (c : ℂ)^2)
    {W : Set (CoeffPair 2)}
    (D : SourceAbelianSpectralChart (by simp) (by norm_num) W
      (hillMiuraDiagonal (P.miura.lift (hillOriginalHminusSource q.val))))
    (k : ℤ) (z : ℂ) (hzr : 0 < z.re) (hzi : z.im ≠ 0) :
    sourceFullAbelianPrimitive (by simp) (by norm_num) W k
      (z,hillMiuraDiagonal (P.miura.lift (hillOriginalHminusSource q.val))) =
      hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q.val) (z^2-P.miura.energyShift) +
        I*(Real.pi : ℂ)*k := by
  let u : PeriodOneRealL2 := ⟨P.miura.lift (hillOriginalHminusSource q.val),hr⟩
  have he := sourceFullAbelianPrimitive_eq_real (hillMiuraRealSource u) D k z
    (sourceCanonicalRootDomain_subset_openGapComplement _ _ _
      (sourceCanonicalRootDomain_of_im_ne_zero _ _ _ (hillMiuraRealSource u).property z hzi))
  rw [P.physical_primitive_squared_frequency q hq hr c hshift z hzr hzi]
  simpa only [hillMiuraRealSource,u] using! he

end NLS.KdV.HillHminusPsiChart
