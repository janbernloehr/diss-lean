import NLS.Fourier.IntrinsicIntervalSobolev
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Closedness of the physical fractional difference graph

Convergence in `L²` admits almost-everywhere convergent subsequences. Applied
to both graph components, this identifies the limiting difference quotient
pointwise almost everywhere. The argument works on every positive interval,
including half regularity, without endpoint conditions.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace NLS.Fourier

/-- Any almost-everywhere property on the normalized circle transfers to physical interval coordinates. -/
theorem ae_interval_coordinates {L : ℝ} (hL : 0 < L) {P : AddCircle (2 : ℝ) → Prop}
    (h : ∀ᵐ x ∂AddCircle.haarAddCircle, P x) :
    ∀ᵐ x ∂volume.restrict (Ioo 0 L), P ((2 / L * x : ℝ) : AddCircle (2 : ℝ)) := by
  have hv : ∀ᵐ x ∂volume, P x := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    exact Measure.ae_smul_measure h _
  have hp : ∀ᵐ (x : ℝ) ∂volume.restrict (Ioc 0 2), P (x : AddCircle (2 : ℝ)) := by
    simpa only [zero_add] using (AddCircle.measurePreserving_mk 2 0).quasiMeasurePreserving.ae hv
  have hp' : ∀ᵐ (x : ℝ) ∂volume.restrict (Ioo 0 ((2 / L) * L)), P (x : AddCircle (2 : ℝ)) := by
    simpa only [div_mul_cancel₀ 2 hL.ne', Measure.restrict_congr_set Ioo_ae_eq_Ioc] using hp
  exact (measurePreserving_interval_dilation (by positivity : 0 < 2 / L) L).quasiMeasurePreserving.ae
    (Measure.ae_smul_measure hp' (ENNReal.ofReal (2 / L)⁻¹))

/-- The physical difference quotient respects simultaneous `L²` limits of both graph components. -/
theorem fractionalDifferenceQuotient_closed {s L : ℝ} (hL : 0 < L)
    {f : ℕ → CircleL2} {g : ℕ → Lp ℂ 2 (intervalProductMeasure L)}
    {F : CircleL2} {G : Lp ℂ 2 (intervalProductMeasure L)}
    (hf : Tendsto f atTop (𝓝 F)) (hg : Tendsto g atTop (𝓝 G))
    (hgraph : ∀ n, (g n : ℝ × ℝ → ℂ) =ᵐ[intervalProductMeasure L]
      fractionalDifferenceQuotient s (intervalPullback L (f n))) :
    fractionalDifferenceQuotient s (intervalPullback L F) =ᵐ[intervalProductMeasure L] G := by
  obtain ⟨ns, hns, hF⟩ := (tendstoInMeasure_of_tendsto_Lp hf).exists_seq_tendsto_ae
  obtain ⟨ms, hms, hG⟩ := (tendstoInMeasure_of_tendsto_Lp (hg.comp hns.tendsto_atTop)).exists_seq_tendsto_ae
  have hphys : ∀ᵐ x ∂volume.restrict (Ioo 0 L),
      Tendsto (fun n => intervalPullback L (f (ns (ms n))) x) atTop (𝓝 (intervalPullback L F x)) := by
    have h := ae_interval_coordinates hL hF
    filter_upwards [h] with x hx
    exact hx.comp hms.tendsto_atTop
  have hx := (Measure.quasiMeasurePreserving_fst
    (μ := volume.restrict (Ioo 0 L)) (ν := volume.restrict (Ioo 0 L))).ae hphys
  have hy := (Measure.quasiMeasurePreserving_snd
    (μ := volume.restrict (Ioo 0 L)) (ν := volume.restrict (Ioo 0 L))).ae hphys
  have he : ∀ᵐ p ∂intervalProductMeasure L, ∀ n,
      g (ns (ms n)) p = fractionalDifferenceQuotient s (intervalPullback L (f (ns (ms n)))) p :=
    ae_all_iff.mpr (fun n => hgraph (ns (ms n)))
  filter_upwards [hx, hy, he, hG] with p hpx hpy hp hlim
  have hQ : Tendsto (fun n => fractionalDifferenceQuotient s (intervalPullback L (f (ns (ms n)))) p)
      atTop (𝓝 (fractionalDifferenceQuotient s (intervalPullback L F) p)) :=
    tendsto_const_nhds.mul (hpx.sub hpy)
  have hlim' : Tendsto (fun n => fractionalDifferenceQuotient s (intervalPullback L (f (ns (ms n)))) p)
      atTop (𝓝 (G p)) := by
    simpa only [Function.comp_def, hp] using hlim
  exact tendsto_nhds_unique hQ hlim'

end NLS.Fourier
