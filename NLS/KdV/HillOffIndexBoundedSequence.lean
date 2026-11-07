import NLS.KdV.HillCanonicalOffIndexBoundedDomain
import NLS.SequenceSpaces.PositiveScalarInfinity
import NLS.SequenceSpaces.BoundedCoordinateAnalytic

/-! The ENTIRE actual correction sequence is analytic as a bounded
sequence, not only one scalar coordinate at a time. The common native
domain and its local bounds precede ALL numerator indices. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.LpSequence
open scoped ENNReal Classical
namespace NLS.KdV

theorem memlp_hillHminusOffIndexAbelianCorrection_infty (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusOffIndexBoundedDomain) :
    Memℓp (positiveScalarExtension (fun n => hillHminusOffIndexAbelianCorrection n q)) ⊤ := by
  obtain ⟨U,_,hqU,_,R,hR,hb⟩ := exists_locally_uniform_hillHminusOffIndexAbelianCorrection_bound q hq
  exact Coeff.memlp_positiveScalarExtension_infty _ ⟨R,hR.le,fun n => (hb q hqU n).2⟩

def hillHminusOffIndexAbelianBoundedSequence (q : PeriodOneHminusOne) : Coeff ⊤ :=
  if hq : q ∈ hillHminusOffIndexBoundedDomain then
    ⟨positiveScalarExtension (fun n => hillHminusOffIndexAbelianCorrection n q),
      memlp_hillHminusOffIndexAbelianCorrection_infty q hq⟩
  else 0

theorem hillHminusOffIndexAbelianBoundedSequence_apply (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusOffIndexBoundedDomain) (k : ℤ) :
    hillHminusOffIndexAbelianBoundedSequence q k =
      positiveScalarExtension (fun n => hillHminusOffIndexAbelianCorrection n q) k := by
  rw [hillHminusOffIndexAbelianBoundedSequence,dif_pos hq]

theorem norm_hillHminusOffIndexAbelianBoundedSequence_le (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusOffIndexBoundedDomain) (R : ℝ) (hR : 0 ≤ R)
    (hb : ∀ n : ℕ+, ‖hillHminusOffIndexAbelianCorrection n q‖ ≤ R) :
    ‖hillHminusOffIndexAbelianBoundedSequence q‖ ≤ R := by
  apply lp.norm_le_of_forall_le hR
  intro k
  rw [hillHminusOffIndexAbelianBoundedSequence_apply q hq]
  exact Coeff.norm_positiveScalarExtension_le _ R hR hb k

theorem analyticOnNhd_hillHminusOffIndexAbelianBoundedSequence_coordinate (k : ℤ) :
    AnalyticOnNhd ℂ (fun q => hillHminusOffIndexAbelianBoundedSequence q k) hillHminusOffIndexBoundedDomain := by
  have hpos : AnalyticOnNhd ℂ
      (fun q => positiveScalarExtension (fun n => hillHminusOffIndexAbelianCorrection n q) k)
      hillHminusOffIndexBoundedDomain := by
    by_cases hk : k ∈ range positiveEmbedding
    · obtain ⟨n,rfl⟩ := hk
      change AnalyticOnNhd ℂ (fun q => positiveScalarExtension (fun n => hillHminusOffIndexAbelianCorrection n q) ((n:ℕ):ℤ)) _
      simpa only [positiveScalarExtension_apply] using
        (analyticOnNhd_hillHminusOffIndexAbelianCorrection n).mono hillHminusOffIndexBoundedDomain_subset_analytic
    · have he (q : PeriodOneHminusOne) : positiveScalarExtension (fun n => hillHminusOffIndexAbelianCorrection n q) k = 0 :=
        positiveScalarExtension_zero_of_not_mem_range _ k hk
      simp only [he]
      exact analyticOnNhd_const
  intro q hq
  apply (hpos q hq).congr
  filter_upwards [isOpen_hillHminusOffIndexBoundedDomain.mem_nhds hq] with a ha
  exact (hillHminusOffIndexAbelianBoundedSequence_apply a ha k).symm

theorem analyticOnNhd_hillHminusOffIndexAbelianBoundedSequence :
    AnalyticOnNhd ℂ hillHminusOffIndexAbelianBoundedSequence hillHminusOffIndexBoundedDomain := by
  intro q hq
  obtain ⟨U,hU,hqU,hUW,R,hR,hb⟩ := exists_locally_uniform_hillHminusOffIndexAbelianCorrection_bound q hq
  have hseq : AnalyticOnNhd ℂ hillHminusOffIndexAbelianBoundedSequence U :=
    Coeff.analyticOnNhd_of_bounded_coordinatewise _ hU
      (fun k => (analyticOnNhd_hillHminusOffIndexAbelianBoundedSequence_coordinate k).mono hUW) R
      (fun a ha => norm_hillHminusOffIndexAbelianBoundedSequence_le a (hUW ha) R hR.le (fun n => (hb a ha n).2))
  exact hseq q hqU

end NLS.KdV
