import NLS.Articles.DNLSEstimates.HigherActions
import NLS.ZakharovShabat.SourceLemma10_11
import NLS.ZakharovShabat.SourceLemmaF1
import NLS.ZakharovShabat.EntirePeriodicProductOrders

/-!
# The original primitive and Appendix A

The paper's F is the zero-index full Abelian primitive. Its domain and
endpoint normalization are fixed independently of its analyticity proof.
The exported common domains exist unconditionally; individual assertions
below retain the actual source, gap and path objects.
-/
noncomputable section
open Set Filter Topology Complex NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.Articles.DNLSEstimates

/-- The paper's primitive, with its original zero-gap normalization. -/
def primitive (W : Set (CoeffPair 2)) : ℂ × CoeffPair 2 → ℂ :=
  sourceFullAbelianPrimitive (by simp) (by norm_num) W 0

/-- Lemma 2's continuation, original circle periods and every piecewise C¹
admissible endpoint path hold on a constructed common complex neighborhood. -/
theorem lemma_two_domain :
    ∃ W : Set (CoeffPair 2), IsOpen W ∧ IsConnected W ∧
      realTypeSourceLocus 2 ⊆ W ∧ SourceLemma10_11Data (by simp) (by norm_num) W :=
  sourceLemma10_11 (by simp) (by norm_num)

/-- Lemma 2(i) on the full open moving-cut domain. The fixed disc-complement
products in the paper are supplied by the same data's `neighborhoods`. -/
theorem lemma_two_joint {W : Set (CoeffPair 2)}
    (L : SourceLemma10_11Data (by simp) (by norm_num) W) :
    IsOpen (sourceCanonicalRootJointDomain (by simp) (by norm_num) W) ∧
    AnalyticOnNhd ℂ (sourceCriticalRootRatioJoint (by simp) (by norm_num))
      (sourceCanonicalRootJointDomain (by simp) (by norm_num) W) :=
  L.previous.previous.previous.joint

/-- Lemma 2(ii), filling every collapsed gap at complex sources too. -/
theorem lemma_two_spectral {W : Set (CoeffPair 2)}
    (L : SourceLemma10_11Data (by simp) (by norm_num) W)
    (a : CoeffPair 2) (ha : a ∈ W) :
    AnalyticOnNhd ℂ (sourceCriticalRootRatioContinued (by simp) (by norm_num) a)
      (sourceOpenGapComplement (by simp) (by norm_num) a) :=
  L.previous.previous.analytic a ha

/-- Lemma 2's closed-circle consequence, on each original isolating circle. -/
theorem lemma_two_circle {W : Set (CoeffPair 2)}
    (L : SourceLemma10_11Data (by simp) (by norm_num) W)
    (a : CoeffPair 2) (ha : a ∈ W) (n : ℤ)
    (C : SourceCriticalRootPeriodCircle (by simp) (by norm_num) a n) :
    (∮ z in C((C.center : ℂ),C.radius),
      sourceCriticalRootRatioJoint (by simp) (by norm_num) (z,a)) = 0 :=
  L.previous.zero a ha n C

/-- Lemma 2(iii) for every admissible piecewise interior-C¹ endpoint path
inside an original isolating disc; the improper limit is part of the result. -/
theorem lemma_two_endpoint_path {W V : Set (CoeffPair 2)}
    (L : SourceLemma10_11Data (by simp) (by norm_num) W)
    {D : ℤ → Set ℂ} {c : ℝ}
    (hD : SourceIsolatingNeighborhoods (by simp) (by norm_num) V D c)
    (a : CoeffPair 2) (haW : a ∈ W) (haV : a ∈ V) (n : ℤ)
    (Γ : PiecewiseInteriorC1Path
      (canonicalPeriodicLeft (by simp) (by norm_num)
        (periodOnePotential a) (periodOnePotential_mem a) n)
      (canonicalPeriodicRight (by simp) (by norm_num)
        (periodOnePotential a) (periodOnePotential_mem a) n))
    (hadm : SourceAdmissiblePiecewisePath (by simp) (by norm_num) a Γ)
    (hinside : ∀ i u, Γ.edge i u ∈ D n) :
    Tendsto (fun t : ℝ × ℝ => Γ.truncatedIntegral
      (fun z => sourceCriticalRootRatioJoint (by simp) (by norm_num) (z,a)) t.1 t.2)
      ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[<] (1 : ℝ))) (𝓝 0) ∧
    Γ.improperIntegral (fun z => sourceCriticalRootRatioJoint (by simp) (by norm_num) (z,a)) = 0 :=
  L.piecewise_paths hD a haW haV n Γ hadm hinside

/-- One primitive domain exists before choosing the potential or spectral
point, and can be chosen inside any prescribed common real neighborhood. -/
theorem primitive_domain (X : Set (CoeffPair 2)) (hX : IsOpen X)
    (hrX : realTypeSourceLocus 2 ⊆ X) :
    ∃ W U : Set (CoeffPair 2), U ⊆ X ∧
      SourceSection19Data (by simp) (by norm_num) W U :=
  exists_sourceSection19Data (by simp) (by norm_num) X hX hrX

/-- Lemma 3(i) and Proposition 20: joint analyticity of the actual F on
the open moving-cut domain, with both spectral and source variables. -/
theorem proposition_twenty {W U : Set (CoeffPair 2)}
    (Q : SourceSection19Data (by simp) (by norm_num) W U) :
    AnalyticOnNhd ℂ (primitive W)
      (sourceCanonicalRootJointDomain (by simp) (by norm_num) U) :=
  Q.analytic 0

/-- Collapsed spectral gaps are filled analytically in F, as required by
Lemma 3(ii), including all complex sources of the common neighborhood. -/
theorem lemma_three_spectral {W U : Set (CoeffPair 2)}
    (Q : SourceSection19Data (by simp) (by norm_num) W U)
    (a : CoeffPair 2) (ha : a ∈ U) :
    AnalyticOnNhd ℂ (fun z => primitive W (z,a))
      (sourceOpenGapComplement (by simp) (by norm_num) a) :=
  Q.spectral_analytic a ha 0

/-- The single endpoint extension has the exact common value -i*n*pi at
both endpoints. Continuity here includes approach through all filled gaps. -/
theorem lemma_three_endpoint {W U : Set (CoeffPair 2)}
    (Q : SourceSection19Data (by simp) (by norm_num) W U)
    (a : CoeffPair 2) (ha : a ∈ U) (n : ℤ) (z : ℂ)
    (hz : z ∈ ({canonicalPeriodicLeft (by simp) (by norm_num)
        (periodOnePotential a) (periodOnePotential_mem a) n,
      canonicalPeriodicRight (by simp) (by norm_num)
        (periodOnePotential a) (periodOnePotential_mem a) n} : Set ℂ)) :
    sourceAbelianEndpointExtension (by simp) (by norm_num) W 0 a z =
        -I*(Real.pi : ℂ)*n ∧
    ContinuousWithinAt (sourceAbelianEndpointExtension (by simp) (by norm_num) W 0 a)
      (insert z (sourceOpenGapComplement (by simp) (by norm_num) a)) z := by
  simpa using Q.endpointExtension_value a ha n 0 z hz

/-- Lemma 3(ii): one extension is continuous simultaneously on the whole
filled spectral domain and all periodic endpoints. Discreteness of the
actual spectrum controls approach through other endpoints. -/
theorem lemma_three_continuous_extension {W U : Set (CoeffPair 2)}
    (Q : SourceSection19Data (by simp) (by norm_num) W U)
    (a : CoeffPair 2) (ha : a ∈ U) :
    ContinuousOn (sourceAbelianEndpointExtension (by simp) (by norm_num) W 0 a)
      (sourceOpenGapComplement (by simp) (by norm_num) a ∪
        periodicSpectrum (by simp) (periodOnePotential a)) := by
  let O := sourceOpenGapComplement (by simp) (by norm_num) a
  let F := sourceAbelianEndpointExtension (by simp) (by norm_num) W 0 a
  obtain ⟨E⟩ := Q.charts a ha
  have hO : IsOpen O := E.discs.isOpen_openGapComplement a E.source_mem
  intro z hz
  by_cases hzO : z ∈ O
  · have he : F =ᶠ[𝓝 z] (fun w => primitive W (w,a)) := by
      filter_upwards [hO.mem_nhds hzO] with w hw
      exact Q.endpointExtension_eqOn a ha 0 hw
    exact ((Q.spectral_analytic a ha 0 z hzO).continuousAt.congr he.symm).continuousWithinAt
  · have hspec : z ∈ periodicSpectrum (by simp) (periodOnePotential a) := hz.resolve_left hzO
    obtain ⟨n,hn⟩ := (canonicalPeriodicEndpoints_exhaustive (by simp) (by norm_num)
      (periodOnePotential a) (periodOnePotential_mem a) z).mp hspec
    have hend : z ∈ ({canonicalPeriodicLeft (by simp) (by norm_num)
          (periodOnePotential a) (periodOnePotential_mem a) n,
        canonicalPeriodicRight (by simp) (by norm_num)
          (periodOnePotential a) (periodOnePotential_mem a) n} : Set ℂ) := by
      simpa only [mem_insert_iff, mem_singleton_iff, eq_comm] using hn
    have hcont := (Q.endpointExtension_value a ha n 0 z hend).2
    obtain ⟨r,hr,hiso⟩ := exists_periodicSpectrum_isolating_closedBall
      (by simp) (periodOnePotential a) z
    have hmem : insert z O ∈ 𝓝[O ∪ periodicSpectrum (by simp) (periodOnePotential a)] z := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z hr),
        self_mem_nhdsWithin] with w hw hws
      rcases hws with hwo | hwsp
      · exact mem_insert_of_mem z hwo
      · exact mem_insert_iff.mpr (Or.inl (hiso w (Metric.ball_subset_closedBall hw) hwsp))
    exact hcont.mono_left (le_inf inf_le_left (Filter.le_principal_iff.mpr hmem))

/-- The defining pair of improper endpoint integrals is the same F;
no free additive constant or substituted primitive is used. -/
theorem primitive_endpoint_integrals {W U : Set (CoeffPair 2)}
    (Q : SourceSection19Data (by simp) (by norm_num) W U)
    (a : CoeffPair 2) (ha : a ∈ U) (z ν : ℂ)
    (hz : z ∈ ({canonicalPeriodicLeft (by simp) (by norm_num)
        (periodOnePotential a) (periodOnePotential_mem a) 0,
      canonicalPeriodicRight (by simp) (by norm_num)
        (periodOnePotential a) (periodOnePotential_mem a) 0} : Set ℂ))
    (hν : ν ∈ sourceCanonicalRootDomain (by simp) (by norm_num) a) :
    sourceAbelianEndpointIntegral (by simp) (by norm_num) a z ν = primitive W (ν,a) ∧
    sourceAbelianEndpointAverage (by simp) (by norm_num) 0 ν a = primitive W (ν,a) :=
  Q.endpoint_integrals a ha 0 z ν hz hν

/-- Lemma 3(iii)'s signed arcosh boundary formula, with F's actual index
zero normalization, for arbitrary upper or lower half-plane approach. -/
theorem lemma_three_boundary {W U : Set (CoeffPair 2)}
    (Q : SourceSection19Data (by simp) (by norm_num) W U)
    (a : realTypeSourceSubmodule 2) (n : ℤ) (upper : Bool) (x : ℝ)
    (hx : x ∈ Icc
      (canonicalPeriodicLeft (by simp) (by norm_num)
        (periodOnePotential a.val) (periodOnePotential_mem a.val) n).re
      (canonicalPeriodicRight (by simp) (by norm_num)
        (periodOnePotential a.val) (periodOnePotential_mem a.val) n).re) :
    Tendsto (fun z => primitive W (z,a.val))
      (𝓝[sourceAbelianHalfPlane upper] (x : ℂ))
      (𝓝 ((if upper then (sourceRealGapArcoshProfile (by simp) a.val n x : ℂ)
        else -(sourceRealGapArcoshProfile (by simp) a.val n x : ℂ)) - I*(Real.pi : ℂ)*n)) := by
  obtain ⟨E⟩ := Q.charts a.val (Q.real_subset a.property)
  simpa [primitive, sub_eq_add_neg] using
    sourceFullAbelianPrimitive_real_gap_boundary_limit_index a E n 0 upper x hx

/-- Lemma 3(iii)'s principal logarithm formula near either real periodic
endpoint. The explicit exponential is the signed factor exp(i*pi*n).
The Floquet multiplier is (Delta + canonicalRoot)/2. -/
theorem lemma_three_local_log {W U : Set (CoeffPair 2)}
    (Q : SourceSection19Data (by simp) (by norm_num) W U)
    (a : realTypeSourceSubmodule 2) (n : ℤ) (z : ℂ)
    (hz : z ∈ ({canonicalPeriodicLeft (by simp) (by norm_num)
        (periodOnePotential a.val) (periodOnePotential_mem a.val) n,
      canonicalPeriodicRight (by simp) (by norm_num)
        (periodOnePotential a.val) (periodOnePotential_mem a.val) n} : Set ℂ)) :
    (fun w => primitive W (w,a.val)) =ᶠ[𝓝[sourceOpenGapComplement (by simp) (by norm_num) a.val] z]
      (fun w => log (exp (I*(Real.pi : ℂ)*n)*
        sourceFloquetMultiplier (by simp) (by norm_num) a.val w) - I*(Real.pi : ℂ)*n) := by
  obtain ⟨E⟩ := Q.charts a.val (Q.real_subset a.property)
  have hi : Tendsto
      (fun w => (sourceFullAbelianPrimitive (by simp) (by norm_num) W n (w,a.val)).im)
      (𝓝[sourceOpenGapComplement (by simp) (by norm_num) a.val] z) (𝓝 0) := by
    simpa [Function.comp_def] using continuous_im.continuousAt.tendsto.comp
      (Q.endpoint_limit a.val (Q.real_subset a.property) n n z hz)
  filter_upwards [self_mem_nhdsWithin,
    hi.eventually (Ioo_mem_nhds (neg_neg_of_pos Real.pi_pos) Real.pi_pos)] with w hw him
  have he : exp (sourceFullAbelianPrimitive (by simp) (by norm_num) W n (w,a.val)) =
      exp (I*(Real.pi : ℂ)*n)*sourceFloquetMultiplier (by simp) (by norm_num) a.val w := by
    rw [sourceFullAbelianPrimitive_eq_real a E n w hw, exp_add,
      sourceAbelianPrimitive_exp (by simp) (by norm_num) a.val a.property w hw, mul_comm]
  rw [← he, log_exp him.1 him.2.le, Q.index_shift a.val (Q.real_subset a.property) n w hw]
  simp only [primitive, add_sub_cancel_right]

/-- The logarithm in Lemma 3(iii) holds in the full relative neighborhood
of every point of the closed real gap, with all off-cut approaches allowed.
Taking the union of these neighborhoods gives a neighborhood of the whole gap. -/
theorem lemma_three_log_near_gap {W U : Set (CoeffPair 2)}
    (Q : SourceSection19Data (by simp) (by norm_num) W U)
    (a : realTypeSourceSubmodule 2) (n : ℤ) (x : ℝ)
    (hx : x ∈ Icc
      (canonicalPeriodicLeft (by simp) (by norm_num)
        (periodOnePotential a.val) (periodOnePotential_mem a.val) n).re
      (canonicalPeriodicRight (by simp) (by norm_num)
        (periodOnePotential a.val) (periodOnePotential_mem a.val) n).re) :
    (fun w => primitive W (w,a.val)) =ᶠ[𝓝[sourceOpenGapComplement (by simp) (by norm_num) a.val] (x : ℂ)]
      (fun w => log (exp (I*(Real.pi : ℂ)*n)*
        sourceFloquetMultiplier (by simp) (by norm_num) a.val w) - I*(Real.pi : ℂ)*n) := by
  let l := canonicalPeriodicLeft (by simp) (by norm_num)
    (periodOnePotential a.val) (periodOnePotential_mem a.val) n
  let r := canonicalPeriodicRight (by simp) (by norm_num)
    (periodOnePotential a.val) (periodOnePotential_mem a.val) n
  have him := canonicalPeriodicEndpoints_im_eq_zero_of_realType (by simp) (by norm_num)
    (periodOnePotential a.val) (periodOnePotential_mem a.val)
    (isRealType_periodOnePotential a.val a.property) n
  by_cases he : x = l.re ∨ x = r.re
  · apply lemma_three_local_log Q a n (x : ℂ)
    rcases he with he | he
    · exact mem_insert_iff.mpr (Or.inl (Complex.ext he (by simpa only [Complex.ofReal_im] using him.1.symm)))
    · exact mem_insert_iff.mpr (Or.inr (mem_singleton_iff.mpr
        (Complex.ext he (by simpa only [Complex.ofReal_im] using him.2.symm))))
  have hxi : x ∈ Ioo l.re r.re :=
    ⟨lt_of_le_of_ne hx.1 (Ne.symm (not_or.mp he).1),
      lt_of_le_of_ne hx.2 (not_or.mp he).2⟩
  have hg : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential a.val) (periodOnePotential_mem a.val) n ≠ 0 := by
    intro hg
    have heq : r = l := sub_eq_zero.mp hg
    have hr := congrArg Complex.re heq
    linarith [hxi.1, hxi.2]
  have hside (upper : Bool) : Tendsto
      (fun w => (sourceFullAbelianPrimitive (by simp) (by norm_num) W n (w,a.val)).im)
      (𝓝[sourceAbelianHalfPlane upper] (x : ℂ)) (𝓝 0) := by
    have h := continuous_im.continuousAt.tendsto.comp (Q.real_gap_boundary a n upper x hx)
    cases upper <;> simpa [Function.comp_def] using h
  have hall := (hside true).sup (hside false)
  rw [← nhdsWithin_union] at hall
  have hmem : sourceAbelianHalfPlane true ∪ sourceAbelianHalfPlane false ∈
      𝓝[sourceOpenGapComplement (by simp) (by norm_num) a.val] (x : ℂ) := by
    have hreal : {w : ℂ | w.re ∈ Ioo l.re r.re} ∈ 𝓝 (x : ℂ) :=
      (continuous_re.tendsto (x : ℂ)).eventually (Ioo_mem_nhds hxi.1 hxi.2)
    filter_upwards [mem_nhdsWithin_of_mem_nhds hreal, self_mem_nhdsWithin] with w hw hwO
    have hwi : w.im ≠ 0 := by
      intro hwim
      have hwseg := sourcePeriodicSegment_mem_of_realIcc (by simp) (by norm_num)
        a.val a.property n w.re ⟨hw.1.le,hw.2.le⟩
      have hwreal : (w.re : ℂ) = w := Complex.ext rfl (by simpa using hwim.symm)
      rw [hwreal] at hwseg
      exact hwO n hg hwseg
    change 0 < w.im ∨ w.im < 0
    exact (lt_or_gt_of_ne hwi).symm
  have hi := hall.mono_left (le_inf inf_le_left (Filter.le_principal_iff.mpr hmem))
  obtain ⟨E⟩ := Q.charts a.val (Q.real_subset a.property)
  filter_upwards [self_mem_nhdsWithin,
    hi.eventually (Ioo_mem_nhds (neg_neg_of_pos Real.pi_pos) Real.pi_pos)] with w hw hwi
  have hexp : exp (sourceFullAbelianPrimitive (by simp) (by norm_num) W n (w,a.val)) =
      exp (I*(Real.pi : ℂ)*n)*sourceFloquetMultiplier (by simp) (by norm_num) a.val w := by
    rw [sourceFullAbelianPrimitive_eq_real a E n w hw, exp_add,
      sourceAbelianPrimitive_exp (by simp) (by norm_num) a.val a.property w hw, mul_comm]
  rw [← hexp, log_exp hwi.1 hwi.2.le, Q.index_shift a.val (Q.real_subset a.property) n w hw]
  simp only [primitive, add_sub_cancel_right]

/-- The unnumbered assertion in Lemma 3: the arcosh profile is continuous
on the closed real gap, positive in its interior, and zero at both ends. -/
theorem gap_profile_properties (a : realTypeSourceSubmodule 2) (n : ℤ) :
    let l := (canonicalPeriodicLeft (by simp) (by norm_num)
      (periodOnePotential a.val) (periodOnePotential_mem a.val) n).re
    let r := (canonicalPeriodicRight (by simp) (by norm_num)
      (periodOnePotential a.val) (periodOnePotential_mem a.val) n).re
    ContinuousOn (sourceRealGapArcoshProfile (by simp) a.val n) (Icc l r) ∧
      sourceRealGapArcoshProfile (by simp) a.val n l = 0 ∧
      sourceRealGapArcoshProfile (by simp) a.val n r = 0 ∧
      ∀ x ∈ Ioo l r, 0 < sourceRealGapArcoshProfile (by simp) a.val n x :=
  sourceRealGapArcoshProfile_spec (by simp) (by norm_num) a.val a.property n

/-- Lemma 3(iv), with the exact zero-potential normalization. -/
theorem lemma_three_zero {W U : Set (CoeffPair 2)}
    (Q : SourceSection19Data (by simp) (by norm_num) W U) (z : ℂ) :
    primitive W (z,0) = -I*z := by
  simpa [primitive] using (Q.zero 0 z).1

/-- Lemma 19(i) and (ii), with the literal half-gap and full-gap constants,
on one constructed open connected complex neighborhood of the real locus. -/
theorem lemma_nineteen :
    ∃ W : Set (CoeffPair 2), IsOpen W ∧ IsConnected W ∧ realTypeSourceLocus 2 ⊆ W ∧
      (∀ a ∈ W, ∀ n : ℤ,
        canonicalPeriodicGap (by simp) (by norm_num)
          (periodOnePotential a) (periodOnePotential_mem a) n = 0 →
        ∃ V : Set (CoeffPair 2), IsOpen V ∧ a ∈ V ∧ V ⊆ W ∧ ∀ b ∈ V,
          ‖canonicalCriticalPoints (by simp) (by norm_num)
              (periodOnePotential b) (periodOnePotential_mem b) n -
            canonicalPeriodicMidpoint (by simp) (by norm_num)
              (periodOnePotential b) (periodOnePotential_mem b) n‖ ≤
          ‖canonicalPeriodicGap (by simp) (by norm_num)
              (periodOnePotential b) (periodOnePotential_mem b) n‖/2) ∧
      (∀ a : CoeffPair 2, IsRealType (CoeffPair.toMax 2 a) →
        ∃ V : Set (CoeffPair 2), IsOpen V ∧ a ∈ V ∧ V ⊆ W ∧ ∀ b ∈ V, ∀ n : ℤ,
          ‖canonicalCriticalPoints (by simp) (by norm_num)
              (periodOnePotential b) (periodOnePotential_mem b) n -
            canonicalPeriodicMidpoint (by simp) (by norm_num)
              (periodOnePotential b) (periodOnePotential_mem b) n‖ ≤
          ‖canonicalPeriodicGap (by simp) (by norm_num)
              (periodOnePotential b) (periodOnePotential_mem b) n‖) :=
  sourceLemmaF1 (by simp) (by norm_num)

end NLS.Articles.DNLSEstimates
