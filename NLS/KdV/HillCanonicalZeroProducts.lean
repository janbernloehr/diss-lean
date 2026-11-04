import NLS.KdV.HillUniformEnergyGapOffsetDomain
import NLS.KdV.HminusOneHillPsiProductContinuity

/-! Literal retained products of the ACTUAL canonical complex zero
sequences. Joint energy/source analyticity and locally uniform SAME
finite cutoffs hold on the common domain before every energy. -/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal Classical
namespace NLS.KdV

def hillHminusCanonicalZeroProduct (n : ℕ+) (t : ℂ × PeriodOneHminusOne) : ℂ :=
  hillEnergySequenceProduct n (t.1,hillHminusCanonicalZeroSequence n t.2)

theorem analyticOnNhd_hillHminusCanonicalZeroProduct (n : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusCanonicalZeroProduct n) (univ ×ˢ hillHminusCanonicalZeroSequenceDomain) := by
  intro t ht
  exact (analyticAt_hillEnergySequenceProduct n _).comp
    (f := fun s : ℂ × PeriodOneHminusOne => (s.1,hillHminusCanonicalZeroSequence n s.2))
    (analyticAt_fst.prod ((analyticOnNhd_hillHminusCanonicalZeroSequence n t.2 ht.2).comp analyticAt_snd))

theorem hillHminusCanonicalZeroProduct_real (n : ℕ+) (E : ℂ) (q : PeriodOneRealHminusOne) :
    hillHminusCanonicalZeroProduct n (E,q.val) = hillHminusPsiLiteralProduct n (E,q) := by
  unfold hillHminusCanonicalZeroProduct hillHminusPsiLiteralProduct
  rw [hillHminusCanonicalZeroSequence_real n q.val q.property]

theorem tendstoLocallyUniformlyOn_hillEnergySequencePartialProduct (n : ℕ+) :
    TendstoLocallyUniformlyOn (hillEnergySequencePartialProduct n) (hillEnergySequenceProduct n) atTop univ := by
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro t _
  obtain ⟨U,hU,ht,hlim⟩ := exists_uniform_hillEnergySequenceProduct_neighborhood n t
  exact ⟨U,nhdsWithin_le_nhds (hU.mem_nhds ht),hlim⟩

theorem tendstoLocallyUniformlyOn_hillHminusCanonicalZeroProduct (n : ℕ+) :
    TendstoLocallyUniformlyOn
      (fun (N : ℕ) (t : ℂ × PeriodOneHminusOne) => hillEnergySequencePartialProduct n N (t.1,hillHminusCanonicalZeroSequence n t.2))
      (hillHminusCanonicalZeroProduct n) atTop (univ ×ˢ hillHminusCanonicalZeroSequenceDomain) := by
  let G : ℂ × PeriodOneHminusOne → ℂ × lp (fun _ : ℕ+ => ℂ) 2 :=
    fun t => (t.1,hillHminusCanonicalZeroSequence n t.2)
  have hG : AnalyticOnNhd ℂ G (univ ×ˢ hillHminusCanonicalZeroSequenceDomain) := by
    intro t ht
    exact analyticAt_fst.prod ((analyticOnNhd_hillHminusCanonicalZeroSequence n t.2 ht.2).comp analyticAt_snd)
  exact (tendstoLocallyUniformlyOn_hillEnergySequencePartialProduct n).comp G
    (mapsTo_univ _ _) hG.continuousOn

end NLS.KdV
