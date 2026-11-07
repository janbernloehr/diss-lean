import NLS.KdV.HillRealCoordinateNontrivial

/-! Each actual original gap has an open dense noncollapsed locus in the
real mean-zero Banach source. Any FINITE collection opens simultaneously
arbitrarily near every real source. Collapsed gaps are included in the domain. -/
noncomputable section
open Set Complex Filter Topology
namespace NLS.KdV

theorem hillRealSignedMap_native_coe (q : HillRealMeanZeroSource) :
    ((hillRealSignedMap q).val : WeightedCoeff (Weight.signedSobolev (-1/2)) 2)=
      hillHminusNativeComplexMap q.val.val := by
  rw [hillRealSignedMap_coe,hillMeanZeroComplexMap_coe]

theorem hillRealPositiveCoordinate_eq_zero_iff_gap (n : ℕ+) (q : HillRealMeanZeroSource) :
    hillRealPositiveCoordinate n q=0 ↔ hillHminusCanonicalGapSquare n q.val.val=0 := by
  have hr : IsRealPeriodOneHminusOne q.val.val := q.property
  have hp := hillHminusNativeComplexMap_action_identity q.val.val
    (real_mem_hillHminusActionAngleNativeDomain _ hr) n
  have hreal := hillHminusNativeComplexMap_conjugate_pair q.val.val hr n
  have hcoef : hillRealPositiveCoordinate n q=(hillHminusNativeComplexMap q.val.val).val (n:ℤ) := by
    rw [hillRealPositiveCoordinate,hillRealSignedMap_native_coe]
  rw [hreal,← hcoef] at hp
  have hI := hillHminusCanonicalAction_eq_zero_iff_gapSquare_of_real q.val.val hr n
  constructor
  · intro hz
    apply hI.mp
    rw [← hp,hz,zero_mul]
  · intro hg
    have hi := hI.mpr hg
    have hz : hillRealPositiveCoordinate n q*(starRingEnd ℂ) (hillRealPositiveCoordinate n q)=0 := hp.trans hi
    rcases mul_eq_zero.mp hz with h | h
    · exact h
    · have hc := congrArg (starRingEnd ℂ) h
      simpa only [Complex.conj_conj,map_zero] using hc

theorem isOpen_hillReal_open_gap (n : ℕ+) :
    IsOpen {q : HillRealMeanZeroSource | hillHminusCanonicalGapSquare n q.val.val ≠ 0} := by
  have he : {q : HillRealMeanZeroSource | hillHminusCanonicalGapSquare n q.val.val ≠ 0}=
      {q | hillRealPositiveCoordinate n q ≠ 0} := by
    ext q
    exact not_congr (hillRealPositiveCoordinate_eq_zero_iff_gap n q).symm
  rw [he]
  exact (isOpen_ne (x := (0:ℂ))).preimage
    (continuous_iff_continuousAt.mpr (fun q => (analyticAt_hillRealPositiveCoordinate n q).continuousAt))

theorem dense_hillReal_open_gap (n : ℕ+) :
    Dense {q : HillRealMeanZeroSource | hillHminusCanonicalGapSquare n q.val.val ≠ 0} := by
  apply (dense_hillRealPositiveCoordinate_ne_zero n).mono
  intro q hq
  exact fun hg => hq ((hillRealPositiveCoordinate_eq_zero_iff_gap n q).mpr hg)

theorem dense_hillReal_finitely_many_open_gaps (S : Finset ℕ+) :
    Dense {q : HillRealMeanZeroSource | ∀ n ∈ S, hillHminusCanonicalGapSquare n q.val.val ≠ 0} := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.notMem_empty,IsEmpty.forall_iff,implies_true,forall_const,ofPred_true] using
      (dense_univ : Dense (univ : Set HillRealMeanZeroSource))
  | @insert n S hn ih =>
    have hd := (dense_hillReal_open_gap n).inter_of_isOpen_left ih (isOpen_hillReal_open_gap n)
    convert hd using 1
    ext q
    simp only [mem_ofPred_eq,mem_inter_iff,Finset.forall_mem_insert]

theorem exists_arbitrarily_near_hillReal_finitely_many_open_gaps (q : HillRealMeanZeroSource)
    (S : Finset ℕ+) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ a : HillRealMeanZeroSource, dist a q < epsilon ∧
      ∀ n ∈ S, hillHminusCanonicalGapSquare n a.val.val ≠ 0 := by
  obtain ⟨a,ha,hgap⟩ := Metric.dense_iff.mp (dense_hillReal_finitely_many_open_gaps S) q epsilon hepsilon
  exact ⟨a,ha,hgap⟩

end NLS.KdV
