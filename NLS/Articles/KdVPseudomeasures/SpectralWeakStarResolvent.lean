import NLS.Articles.KdVPseudomeasures.SourceWeakStarLimits
import NLS.Articles.KdVPseudomeasures.SpectralCrossOrder
import NLS.KdV.SingularHillResolventFamily

/-! The actual full-domain resolvent and finite spectral projection ranks on
bounded sets of original potentials with their physical weak-star topology. -/
noncomputable section
open Set Filter Topology Metric
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.KdV

/-- Bounded physical weak-star sets include continuously into original H-minus-one. -/
theorem continuous_sourceHminusOne_on_bounded (r : ℝ) (hr : AdmissiblePredualOrder r)
    (A : Set (WeakStarPotential r)) (hb : PotentialNormBounded r A) :
    Continuous (fun q : A => potentialHminusOne r hr q.val.toPotential) := by
  have hc := (isEmbedding_sourceLowerDistribution_on_bounded r (-1) (p := 2)
    (by norm_num) (admissible_hminusOne_threshold r hr) A hb).continuous
  convert hc using 1
  funext q
  exact (sourceLowerDistribution_eq_potentialHminusOne r hr q.val).symm

/-- The complement of the actual source spectrum is the full original resolvent. -/
theorem source_not_mem_spectrum_iff_singular_resolvent (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : Potential r) (z : ℂ) :
    z ∉ sourceHillSpectrum r hr q.val ↔ z ∈ singularHillResolventSet (potentialHminusOne r hr q) := by
  change (¬¬Function.Bijective (singularHillOperator (potentialHminusOne r hr q)-
    z • singularHillDomainInclusion)) ↔ _
  exact not_not

/-- The JOINT physical resolvent locus is open in bounded weak-star parameters
and the complex spectral parameter. -/
theorem isOpen_sourceJointResolvent_on_bounded (r : ℝ) (hr : AdmissiblePredualOrder r)
    (A : Set (WeakStarPotential r)) (hb : PotentialNormBounded r A) :
    IsOpen {p : A × ℂ | p.2 ∉ sourceHillSpectrum r hr p.1.val.toPotential.val} := by
  have hc : Continuous (fun p : A × ℂ => (potentialHminusOne r hr p.1.val.toPotential,p.2)) :=
    ((continuous_sourceHminusOne_on_bounded r hr A hb).comp continuous_fst).prodMk continuous_snd
  convert isOpen_singularHillJointResolvent.preimage hc using 1
  ext p
  exact source_not_mem_spectrum_iff_singular_resolvent r hr p.1.val.toPotential p.2

/-- Norm-continuity of the full original H1-valued inverse at every physical
resolvent pair, for bounded weak-star potentials. -/
theorem continuousAt_sourceResolventToH1_on_bounded (r : ℝ) (hr : AdmissiblePredualOrder r)
    (A : Set (WeakStarPotential r)) (hb : PotentialNormBounded r A) (p : A × ℂ)
    (hp : p.2 ∉ sourceHillSpectrum r hr p.1.val.toPotential.val) :
    ContinuousAt (fun x : A × ℂ => singularHillResolventToH1
      (potentialHminusOne r hr x.1.val.toPotential) x.2) p := by
  have hc : Continuous (fun p : A × ℂ => (potentialHminusOne r hr p.1.val.toPotential,p.2)) :=
    ((continuous_sourceHminusOne_on_bounded r hr A hb).comp continuous_fst).prodMk continuous_snd
  exact (analyticAt_singularHillResolventToH1_joint
    (potentialHminusOne r hr p.1.val.toPotential,p.2)
    ((source_not_mem_spectrum_iff_singular_resolvent r hr p.1.val.toPotential p.2).mp hp)).continuousAt.comp
      (f := fun x : A × ℂ => (potentialHminusOne r hr x.1.val.toPotential,x.2)) hc.continuousAt

/-- Norm-continuity of the actual compact original H-minus-one resolvent. -/
theorem continuousAt_sourceBaseResolvent_on_bounded (r : ℝ) (hr : AdmissiblePredualOrder r)
    (A : Set (WeakStarPotential r)) (hb : PotentialNormBounded r A) (p : A × ℂ)
    (hp : p.2 ∉ sourceHillSpectrum r hr p.1.val.toPotential.val) :
    ContinuousAt (fun x : A × ℂ => singularHillBaseResolvent
      (potentialHminusOne r hr x.1.val.toPotential) x.2) p := by
  have hc : Continuous (fun p : A × ℂ => (potentialHminusOne r hr p.1.val.toPotential,p.2)) :=
    ((continuous_sourceHminusOne_on_bounded r hr A hb).comp continuous_fst).prodMk continuous_snd
  exact (analyticAt_singularHillBaseResolvent_joint
    (potentialHminusOne r hr p.1.val.toPotential,p.2)
    ((source_not_mem_spectrum_iff_singular_resolvent r hr p.1.val.toPotential p.2).mp hp)).continuousAt.comp
      (f := fun x : A × ℂ => (potentialHminusOne r hr x.1.val.toPotential,x.2)) hc.continuousAt

/-- Actual membership of a fixed complex spectral value is weak-star closed
within every original norm-bounded physical set. -/
theorem isClosed_sourceSpectralValue_on_bounded (r : ℝ) (hr : AdmissiblePredualOrder r)
    (A : Set (WeakStarPotential r)) (hb : PotentialNormBounded r A) (z : ℂ) :
    IsClosed {q : A | z ∈ sourceHillSpectrum r hr q.val.toPotential.val} := by
  have ho := (isOpen_sourceJointResolvent_on_bounded r hr A hb).preimage
    (continuous_id.prodMk (continuous_const : Continuous (fun _ : A => z)))
  convert ho.isClosed_compl using 1
  ext q
  simp only [mem_compl_iff, mem_preimage, mem_ofPred_eq, Function.id_def, not_not]

/-- The original H-minus-one actual circular Riesz projection. -/
def sourceWeakStarRieszProjection (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : WeakStarPotential r) (c : ℂ) (ρ : ℝ) :
    FourierLebesgueSpace (2:ℝ) (-1) 2 →L[ℂ] FourierLebesgueSpace (2:ℝ) (-1) 2 :=
  singularHillRieszProjection (potentialHminusOne r hr q.toPotential) c ρ

/-- This is the SAME verified physical endpoint projection, not a surrogate. -/
theorem sourceWeakStarRieszProjection_eq_endpoint (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : WeakStarPotential r) (c : ℂ) (ρ : ℝ) :
    sourceWeakStarRieszProjection r hr q c ρ =
      endpointHillRieszProjection r hr.2 (sourceEndpointCoefficients r q.toPotential.val) c ρ := by
  unfold sourceWeakStarRieszProjection
  rw [← sourceEndpointCoefficients_HminusOne r hr q.toPotential]
  rfl

/-- A source physical resolvent circle is precisely a circle for the actual
endpoint resolvent, with the entire original distribution retained. -/
theorem source_resolventCircle_endpoint (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : WeakStarPotential r) (c : ℂ) (ρ : ℝ)
    (hc : ∀ z ∈ sphere c ρ, z ∉ sourceHillSpectrum r hr q.toPotential.val) :
    sphere c ρ ⊆ endpointHillResolventSet r hr.2 (sourceEndpointCoefficients r q.toPotential.val) := by
  intro z hz
  have hh := hc z hz
  rw [sourceHillSpectrum_eq] at hh
  exact not_not.mp hh

/-- Validity of an ENTIRE compact resolvent circle is weak-star open on a
bounded original physical set. -/
theorem isOpen_sourceResolventCircle_on_bounded (r : ℝ) (hr : AdmissiblePredualOrder r)
    (A : Set (WeakStarPotential r)) (hb : PotentialNormBounded r A) (c : ℂ) (ρ : ℝ) :
    IsOpen {q : A | ∀ z ∈ sphere c ρ, z ∉ sourceHillSpectrum r hr q.val.toPotential.val} := by
  convert (isOpen_singularHillResolventCircle c ρ).preimage
    (continuous_sourceHminusOne_on_bounded r hr A hb) using 1
  ext q
  exact forall_congr' (fun z => forall_congr' (fun _ =>
    source_not_mem_spectrum_iff_singular_resolvent r hr q.val.toPotential z))

/-- The actual Riesz projection varies in operator norm on its full circle locus. -/
theorem continuousOn_sourceWeakStarRieszProjection (r : ℝ) (hr : AdmissiblePredualOrder r)
    (A : Set (WeakStarPotential r)) (hb : PotentialNormBounded r A) (c : ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ContinuousOn (fun q : A => sourceWeakStarRieszProjection r hr q.val c ρ)
      {q : A | ∀ z ∈ sphere c ρ, z ∉ sourceHillSpectrum r hr q.val.toPotential.val} :=
  continuousOn_singularHillRieszProjection _ _
    (continuous_sourceHminusOne_on_bounded r hr A hb).continuousOn c ρ hρ
      (fun q hq z hz => (source_not_mem_spectrum_iff_singular_resolvent r hr q.val.toPotential z).mp (hq z hz))

/-- Every valid original physical circle defines an actual idempotent. -/
theorem isIdempotentElem_sourceWeakStarRieszProjection (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : WeakStarPotential r) (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hc : ∀ z ∈ sphere c ρ, z ∉ sourceHillSpectrum r hr q.toPotential.val) :
    IsIdempotentElem (sourceWeakStarRieszProjection r hr q c ρ) := by
  rw [sourceWeakStarRieszProjection_eq_endpoint]
  exact isIdempotentElem_endpointHillRieszProjection r hr.2 _ c ρ hρ
    (source_resolventCircle_endpoint r hr q c ρ hc)

/-- The actual original physical spectral range has finite dimension. -/
theorem finiteDimensional_sourceWeakStarRieszProjection_range (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : WeakStarPotential r) (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hc : ∀ z ∈ sphere c ρ, z ∉ sourceHillSpectrum r hr q.toPotential.val) :
    FiniteDimensional ℂ (sourceWeakStarRieszProjection r hr q c ρ).range := by
  rw [sourceWeakStarRieszProjection_eq_endpoint]
  exact finiteDimensional_endpointHillRieszProjection_range r hr.2 _ c ρ hρ
    (source_resolventCircle_endpoint r hr q c ρ hc)

/-- The actual projection rank is locally constant on the full weak-star open
circle locus. This includes repeated eigenvalues and collapsed gaps. -/
theorem isLocallyConstant_sourceWeakStarRieszProjection_rank (r : ℝ) (hr : AdmissiblePredualOrder r)
    (A : Set (WeakStarPotential r)) (hb : PotentialNormBounded r A) (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) :
    IsLocallyConstant (fun q : {q : A | ∀ z ∈ sphere c ρ,
      z ∉ sourceHillSpectrum r hr q.val.toPotential.val} =>
      Module.finrank ℂ (sourceWeakStarRieszProjection r hr q.val.val c ρ).range) := by
  let U := {q : A | ∀ z ∈ sphere c ρ, z ∉ sourceHillSpectrum r hr q.val.toPotential.val}
  let P (q : U) := sourceWeakStarRieszProjection r hr q.val.val c ρ
  have hP : Continuous P := continuousOn_iff_continuous_domRestrict.mp
    (continuousOn_sourceWeakStarRieszProjection r hr A hb c ρ hρ.le)
  rw [IsLocallyConstant.iff_eventually_eq]
  intro q
  have he := hP.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds (P q) zero_lt_one)
  filter_upwards [he] with v hv
  let : FiniteDimensional ℂ (P q).range :=
    finiteDimensional_sourceWeakStarRieszProjection_range r hr q.val.val c ρ hρ q.property
  let : FiniteDimensional ℂ (P v).range :=
    finiteDimensional_sourceWeakStarRieszProjection_range r hr v.val.val c ρ hρ v.property
  exact ProjectionRank.finrank_eq_of_norm_sub_lt_one (P v) (P q)
    (isIdempotentElem_sourceWeakStarRieszProjection r hr v.val.val c ρ hρ v.property)
    (isIdempotentElem_sourceWeakStarRieszProjection r hr q.val.val c ρ hρ q.property)
    (by simpa only [mem_preimage, Metric.mem_ball, dist_eq_norm] using hv)

/-- A valid physical circle and its ACTUAL finite rank persist throughout a
weak-star neighborhood inside any original endpoint norm-bounded set. -/
theorem eventually_sourceWeakStarRieszProjection_rank_eq (r : ℝ) (hr : AdmissiblePredualOrder r)
    (A : Set (WeakStarPotential r)) (hb : PotentialNormBounded r A) (q : A)
    (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hc : ∀ z ∈ sphere c ρ, z ∉ sourceHillSpectrum r hr q.val.toPotential.val) :
    ∀ᶠ v : A in 𝓝 q,
      (∀ z ∈ sphere c ρ, z ∉ sourceHillSpectrum r hr v.val.toPotential.val) ∧
      Module.finrank ℂ (sourceWeakStarRieszProjection r hr v.val c ρ).range =
        Module.finrank ℂ (sourceWeakStarRieszProjection r hr q.val c ρ).range := by
  have hU := isOpen_sourceResolventCircle_on_bounded r hr A hb c ρ
  have hu := hU.mem_nhds hc
  have hp := (continuousOn_sourceWeakStarRieszProjection r hr A hb c ρ hρ.le).continuousAt hu
  have he := hp.preimage_mem_nhds (Metric.ball_mem_nhds
    (sourceWeakStarRieszProjection r hr q.val c ρ) zero_lt_one)
  filter_upwards [hu, he] with v hv hn
  refine ⟨hv, ?_⟩
  let : FiniteDimensional ℂ (sourceWeakStarRieszProjection r hr q.val c ρ).range :=
    finiteDimensional_sourceWeakStarRieszProjection_range r hr q.val c ρ hρ hc
  let : FiniteDimensional ℂ (sourceWeakStarRieszProjection r hr v.val c ρ).range :=
    finiteDimensional_sourceWeakStarRieszProjection_range r hr v.val c ρ hρ hv
  exact ProjectionRank.finrank_eq_of_norm_sub_lt_one _ _
    (isIdempotentElem_sourceWeakStarRieszProjection r hr v.val c ρ hρ hv)
    (isIdempotentElem_sourceWeakStarRieszProjection r hr q.val c ρ hρ hc)
    (by simpa only [mem_preimage, Metric.mem_ball, dist_eq_norm] using hn)

/-- Only finitely many ACTUAL physical spectral values lie inside any fixed disk. -/
theorem finite_sourceCircleSpectrum (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : WeakStarPotential r) (c : ℂ) (ρ : ℝ) :
    {z : ℂ | z ∈ sourceHillSpectrum r hr q.toPotential.val ∧ z ∈ ball c ρ}.Finite := by
  apply (sourceHillSpectrum_finite_norm_le r hr q.toPotential.val (‖c‖+ρ)).subset
  intro z hz
  refine ⟨hz.1, ?_⟩
  have hh : ‖z-c‖ < ρ := by simpa only [mem_ball, dist_eq_norm] using hz.2
  calc
    ‖z‖ = ‖(z-c)+c‖ := by rw [sub_add_cancel]
    _ ≤ ‖z-c‖+‖c‖ := norm_add_le _ _
    _ ≤ ‖c‖+ρ := by linarith

/-- The actual finite enclosed spectrum, with no supplied eigenvalue list. -/
def sourceCircleSpectrum (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : WeakStarPotential r) (c : ℂ) (ρ : ℝ) : Finset ℂ :=
  (finite_sourceCircleSpectrum r hr q c ρ).toFinset

/-- Membership retains the full original physical spectrum and exact open disk. -/
theorem mem_sourceCircleSpectrum (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : WeakStarPotential r) (c : ℂ) (ρ : ℝ) (z : ℂ) :
    z ∈ sourceCircleSpectrum r hr q c ρ ↔
      z ∈ sourceHillSpectrum r hr q.toPotential.val ∧ z ∈ ball c ρ :=
  (finite_sourceCircleSpectrum r hr q c ρ).mem_toFinset

/-- The actual enclosed algebraic count uses full physical root-space dimensions. -/
def sourceCircleAlgebraicCount (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : WeakStarPotential r) (c : ℂ) (ρ : ℝ) : ℕ :=
  ∑ z ∈ sourceCircleSpectrum r hr q c ρ, sourceHillAlgebraicMultiplicity r hr q.toPotential.val z

/-- The original projection range equals the sum over the ACTUAL enclosed
physical root spaces, including every algebraic chain. -/
theorem sourceWeakStarRieszProjection_range_eq_roots (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : WeakStarPotential r) (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hc : ∀ z ∈ sphere c ρ, z ∉ sourceHillSpectrum r hr q.toPotential.val) :
    (sourceWeakStarRieszProjection r hr q c ρ).range =
      ⨆ z : sourceCircleSpectrum r hr q c ρ,
        singularHillRootSpaceTop (sourceComplexHminusOne r hr q.toPotential.val) z.val := by
  obtain ⟨a, ha⟩ := endpointHillResolventSet_nonempty r hr.1 hr.2
    (sourceEndpointCoefficients r q.toPotential.val)
  have hreal : (endpointHillHminusOne SpectralWeight.one r hr.2
      (sourceEndpointCoefficients r q.toPotential.val)).val =
      (endpointHillHminusOne SpectralWeight.one r hr.2
      (sourceEndpointCoefficients r q.toPotential.val)).val.conjugate := by
    rw [sourceEndpointCoefficients_HminusOne_complex r hr q.toPotential.val,
      sourceComplexHminusOne_val r hr q.toPotential.val]
    exact q.toPotential.property.1
  have he := endpointHillRieszProjection_range_eq_roots r hr.2
    (sourceEndpointCoefficients r q.toPotential.val) hreal c ρ hρ
    (source_resolventCircle_endpoint r hr q c ρ hc) a ha
  rw [sourceEndpointCoefficients_HminusOne_complex r hr q.toPotential.val] at he
  rw [sourceWeakStarRieszProjection_eq_endpoint, he]
  apply le_antisymm
  · apply iSup_le
    intro z
    by_cases hz : z.val ∈ sourceHillSpectrum r hr q.toPotential.val
    · exact le_iSup_of_le ⟨z.val, (mem_sourceCircleSpectrum r hr q c ρ z.val).mpr ⟨hz, z.property⟩⟩ le_rfl
    · rw [sourceHillRootSpaceTop_eq_bot_of_not_mem_spectrum r hr q.toPotential.val z.val hz]
      exact bot_le
  · apply iSup_le
    intro z
    exact le_iSup_of_le ⟨z.val, ((mem_sourceCircleSpectrum r hr q c ρ z.val).mp z.property).2⟩ le_rfl

/-- Rank is the sum of ACTUAL physical algebraic multiplicities enclosed by the circle. -/
theorem sourceWeakStarRieszProjection_rank_eq_count (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : WeakStarPotential r) (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hc : ∀ z ∈ sphere c ρ, z ∉ sourceHillSpectrum r hr q.toPotential.val) :
    Module.finrank ℂ (sourceWeakStarRieszProjection r hr q c ρ).range =
      sourceCircleAlgebraicCount r hr q c ρ := by
  let V := fun z : sourceCircleSpectrum r hr q c ρ =>
    singularHillRootSpaceTop (sourceComplexHminusOne r hr q.toPotential.val) z.val
  let (z : sourceCircleSpectrum r hr q c ρ) : FiniteDimensional ℂ (V z) :=
    finiteDimensional_sourceHillRootSpaceTop r hr q.toPotential.val z.val
  have hind : iSupIndep V :=
    (independent_sourceHillRootSpaceTop r hr q.toPotential.val).comp Subtype.val_injective
  have he := NLS.FunctionalAnalysis.finrank_iSup_of_iSupIndep V hind
  rw [← sourceWeakStarRieszProjection_range_eq_roots r hr q c ρ hρ hc] at he
  change Module.finrank ℂ (sourceWeakStarRieszProjection r hr q c ρ).range =
    ∑ z : sourceCircleSpectrum r hr q c ρ, sourceHillAlgebraicMultiplicity r hr q.toPotential.val z.val at he
  simpa only [sourceCircleAlgebraicCount, Finset.sum_coe_sort] using he

/-- The ACTUAL enclosed algebraic count is stable on a weak-star neighborhood
of each bounded physical potential with a valid resolvent circle. -/
theorem eventually_sourceCircleAlgebraicCount_eq (r : ℝ) (hr : AdmissiblePredualOrder r)
    (A : Set (WeakStarPotential r)) (hb : PotentialNormBounded r A) (q : A)
    (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hc : ∀ z ∈ sphere c ρ, z ∉ sourceHillSpectrum r hr q.val.toPotential.val) :
    ∀ᶠ v : A in 𝓝 q,
      (∀ z ∈ sphere c ρ, z ∉ sourceHillSpectrum r hr v.val.toPotential.val) ∧
      sourceCircleAlgebraicCount r hr v.val c ρ = sourceCircleAlgebraicCount r hr q.val c ρ := by
  filter_upwards [eventually_sourceWeakStarRieszProjection_rank_eq r hr A hb q c ρ hρ hc] with v hv
  refine ⟨hv.1, ?_⟩
  rw [← sourceWeakStarRieszProjection_rank_eq_count r hr v.val c ρ hρ hv.1,
    ← sourceWeakStarRieszProjection_rank_eq_count r hr q.val c ρ hρ hc]
  exact hv.2

end NLS.Articles.KdVPseudomeasures
