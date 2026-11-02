import NLS.Articles.KdVPseudomeasures.SpectralFreeCount
import NLS.KdV.PseudomeasureRieszProjection
import NLS.ComplexAnalysis.RealDiameterDisc

/-!
# A central physical spectral projection and its homotopy-invariant rank

One diameter circle works on an entire original real source norm ball. Its
actual H-minus-one Riesz projection has finite rank, and that rank is unchanged
along the original potential homotopy. Identification of this rank with the
sum of physical algebraic multiplicities remains a separate obligation.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue NLS.KdV

/-- Center of the real-diameter circle enclosing the actual central spectrum. -/
def sourceCentralCircleCenter (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) (N : ℕ) : ℂ :=
  ((-sourceSpectralBound r hr R-1+(freeHillValue N-12*(N:ℝ)))/2:ℝ)

/-- Radius of the common central physical resolvent circle. -/
def sourceCentralCircleRadius (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) (N : ℕ) : ℝ :=
  ((freeHillValue N-12*(N:ℝ))-(-sourceSpectralBound r hr R-1))/2

theorem sourceCentralCircleRadius_pos (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ)
    (N : ℕ) (hN : 2 ≤ N) : 0 < sourceCentralCircleRadius r hr R N := by
  unfold sourceCentralCircleRadius
  linarith [sourceCentralWindow_left_lt_right r hr R N hN]

/-- The entire circle is in the full physical resolvent for every native real
original source potential on the given norm ball. -/
theorem sourceCentralCircle_bijective (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ)
    (N : ℕ) (hN : 2 ≤ N)
    (hcut : 13*endpointHillConstant r*(N:ℝ)^(r-1/2)*R ≤ 1/2)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (hq : ‖q‖ ≤ R)
    (hreal : q.val = q.val.conjugate) (z : ℂ)
    (hz : z ∈ sphere (sourceCentralCircleCenter r hr R N) (sourceCentralCircleRadius r hr R N)) :
    Function.Bijective (singularHillOperator (sourceComplexHminusOne r hr q)-z • singularHillDomainInclusion) := by
  by_contra hnot
  have him := sourceHillSpectrum_im_eq_zero r hr q hreal z hnot
  have he : (z.re:ℂ) = z := by apply Complex.ext <;> simp [him]
  have hz' := (ComplexAnalysis.ofReal_mem_realDiameter_sphere_iff
    (-sourceSpectralBound r hr R-1) (freeHillValue N-12*(N:ℝ)) z.re
    (sourceCentralWindow_left_lt_right r hr R N hN).le).mp (he.symm ▸ hz)
  have hb : z ∈ sourceCentralWindowBoundary r hr R N := by
    have hh : |z.im| ≤ sourceCentralWindowHeight r hr R N := by
      rw [him,abs_zero]
      exact (sourceCentralWindowHeight_pos r hr R N).le
    rcases hz' with hz' | hz'
    · exact Or.inl ⟨hz',hh⟩
    · exact Or.inr (Or.inl ⟨hz',hh⟩)
  exact hnot (sourceCentralWindowBoundary_bijective r hr R N hN hcut q hq z hb)

/-- On the actual real source spectrum, circle interior means exactly central membership. -/
theorem sourceHillSpectrum_mem_centralCircle_iff (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ)
    (N : ℕ) (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (hq : ‖q‖ ≤ R)
    (hreal : q.val = q.val.conjugate) (z : ℂ) (hz : z ∈ sourceHillSpectrum r hr q) :
    z ∈ ball (sourceCentralCircleCenter r hr R N) (sourceCentralCircleRadius r hr R N) ↔
      z ∈ sourceCentralSpectrum r hr q N := by
  have him := sourceHillSpectrum_im_eq_zero r hr q hreal z hz
  have he : (z.re:ℂ) = z := by apply Complex.ext <;> simp [him]
  have hb : z ∈ ball (sourceCentralCircleCenter r hr R N) (sourceCentralCircleRadius r hr R N) ↔
      -sourceSpectralBound r hr R-1 < z.re ∧ z.re < freeHillValue N-12*(N:ℝ) := by
    rw [← he]
    exact ComplexAnalysis.ofReal_mem_realDiameter_ball_iff _ _ _
  rw [hb,mem_sourceCentralSpectrum]
  have hlo : -sourceSpectralBound r hr R-1 < z.re := by
    linarith [sourceHillSpectrum_re_lower_bound_on_ball r hr R q hq z hz]
  simp only [hz,hlo,true_and]

/-- The same original circle belongs to the identical endpoint physical resolvent. -/
theorem sourceCentralCircle_subset_resolvent (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ)
    (N : ℕ) (hN : 2 ≤ N)
    (hcut : 13*endpointHillConstant r*(N:ℝ)^(r-1/2)*R ≤ 1/2)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (hq : ‖q‖ ≤ R)
    (hreal : q.val = q.val.conjugate) :
    sphere (sourceCentralCircleCenter r hr R N) (sourceCentralCircleRadius r hr R N) ⊆
      endpointHillResolventSet r hr.2 (sourceEndpointCoefficients r q) := by
  intro z hz
  change Function.Bijective (singularHillOperator
    (endpointHillHminusOne SpectralWeight.one r hr.2 (sourceEndpointCoefficients r q))-
      z • singularHillDomainInclusion)
  rw [sourceEndpointCoefficients_HminusOne_complex]
  exact sourceCentralCircle_bijective r hr R N hN hcut q hq hreal z hz

/-- The actual central circle integral acts on the original H-minus-one base space. -/
def sourceCentralProjection (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) (N : ℕ)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) :
    FourierLebesgueSpace (2:ℝ) (-1) 2 →L[ℂ] FourierLebesgueSpace (2:ℝ) (-1) 2 :=
  endpointHillRieszProjection r hr.2 (sourceEndpointCoefficients r q)
    (sourceCentralCircleCenter r hr R N) (sourceCentralCircleRadius r hr R N)

/-- The central projection is idempotent on the full original base space. -/
theorem isIdempotentElem_sourceCentralProjection (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ)
    (N : ℕ) (hN : 2 ≤ N)
    (hcut : 13*endpointHillConstant r*(N:ℝ)^(r-1/2)*R ≤ 1/2)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (hq : ‖q‖ ≤ R) (hreal : q.val = q.val.conjugate) :
    IsIdempotentElem (sourceCentralProjection r hr R N q) :=
  isIdempotentElem_endpointHillRieszProjection r hr.2 _ _ _
    (sourceCentralCircleRadius_pos r hr R N hN)
    (sourceCentralCircle_subset_resolvent r hr R N hN hcut q hq hreal)

/-- The actual central spectral range is finite dimensional. -/
theorem finiteDimensional_sourceCentralProjection_range (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ)
    (N : ℕ) (hN : 2 ≤ N)
    (hcut : 13*endpointHillConstant r*(N:ℝ)^(r-1/2)*R ≤ 1/2)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (hq : ‖q‖ ≤ R) (hreal : q.val = q.val.conjugate) :
    FiniteDimensional ℂ (sourceCentralProjection r hr R N q).range :=
  finiteDimensional_endpointHillRieszProjection_range r hr.2 _ _ _
    (sourceCentralCircleRadius_pos r hr R N hN)
    (sourceCentralCircle_subset_resolvent r hr R N hN hcut q hq hreal)

/-- The actual central projection is operator-norm continuous on the original real norm ball. -/
theorem continuousOn_sourceCentralProjection (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ)
    (N : ℕ) (hN : 2 ≤ N)
    (hcut : 13*endpointHillConstant r*(N:ℝ)^(r-1/2)*R ≤ 1/2) :
    ContinuousOn (sourceCentralProjection r hr R N)
      {q : FourierLebesgueSpace (2:ℝ) (-r) ⊤ | ‖q‖ ≤ R ∧ q.val = q.val.conjugate} :=
  continuousOn_endpointHillRieszProjection r hr.2 (sourceEndpointCoefficients r) _
    (sourceEndpointCoefficientsCLM r).continuous.continuousOn _ _
    (sourceCentralCircleRadius_pos r hr R N hN).le
    (fun q hq => sourceCentralCircle_subset_resolvent r hr R N hN hcut q hq.1 hq.2)

/-- Every original physical central eigenvector is fixed by the actual central projection. -/
theorem sourceCentralProjection_eigenvector (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ)
    (N : ℕ) (hN : 2 ≤ N)
    (hcut : 13*endpointHillConstant r*(N:ℝ)^(r-1/2)*R ≤ 1/2)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (hq : ‖q‖ ≤ R) (hreal : q.val = q.val.conjugate)
    (z : ℂ) (hz : z ∈ sourceCentralSpectrum r hr q N)
    (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : singularHillOperator (sourceComplexHminusOne r hr q) f = z • singularHillDomainInclusion f) :
    sourceCentralProjection r hr R N q (singularHillDomainInclusion f) = singularHillDomainInclusion f := by
  apply endpointHillRieszProjection_eigenvector_inside r hr.2 _ _ _
    (sourceCentralCircleRadius_pos r hr R N hN)
    (sourceCentralCircle_subset_resolvent r hr R N hN hcut q hq hreal) z
  · exact (sourceHillSpectrum_mem_centralCircle_iff r hr R N q hq hreal z
      ((mem_sourceCentralSpectrum r hr q N z).mp hz).1).mpr hz
  · rwa [sourceEndpointCoefficients_HminusOne_complex]

/-- Real scalar multiplication preserves native distributional reality. -/
theorem source_real_smul (r : ℝ) (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤)
    (hreal : q.val = q.val.conjugate) (t : ℝ) :
    ((t:ℂ) • q).val = ((t:ℂ) • q).val.conjugate := by
  ext f
  have he := congrArg (fun u : Distribution (2:ℝ) => u f) hreal
  change q.val f = star (q.val f.conjugate) at he
  change (t:ℂ)*q.val f = star ((t:ℂ)*q.val f.conjugate)
  rw [star_mul,he]
  simp only [Complex.star_def,Complex.conj_ofReal]
  ring

/-- The actual central projection rank is unchanged along the original potential
homotopy from zero to q. This does not yet identify rank with algebraic count. -/
theorem sourceCentralProjection_rank_eq_zero (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ)
    (N : ℕ) (hN : 2 ≤ N)
    (hcut : 13*endpointHillConstant r*(N:ℝ)^(r-1/2)*R ≤ 1/2)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (hq : ‖q‖ ≤ R) (hreal : q.val = q.val.conjugate) :
    Module.finrank ℂ (sourceCentralProjection r hr R N q).range =
      Module.finrank ℂ (sourceCentralProjection r hr R N 0).range := by
  let Q : ℝ → WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ :=
    fun t => sourceEndpointCoefficients r ((t:ℂ) • q)
  have hQ : Continuous Q := (sourceEndpointCoefficientsCLM r).continuous.comp
    (Complex.continuous_ofReal.smul continuous_const)
  have hn (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : ‖(t:ℂ) • q‖ ≤ R := by
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg q) ht.2).trans hq
  have hc (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      sphere (sourceCentralCircleCenter r hr R N) (sourceCentralCircleRadius r hr R N) ⊆
        endpointHillResolventSet r hr.2 (Q t) :=
    sourceCentralCircle_subset_resolvent r hr R N hN hcut _ (hn t ht) (source_real_smul r q hreal t)
  have he := endpointHillRieszProjection_rank_eq r hr.2 Q (Icc (0:ℝ) 1) isPreconnected_Icc
    hQ.continuousOn _ _ (sourceCentralCircleRadius_pos r hr R N hN) hc
    (a := 1) (b := 0) (by norm_num) (by norm_num)
  have h1 : Q 1 = sourceEndpointCoefficients r q := by simp only [Q,Complex.ofReal_one,one_smul]
  have h0 : Q 0 = sourceEndpointCoefficients r 0 := by simp only [Q,Complex.ofReal_zero,zero_smul]
  rw [h1,h0] at he
  exact he

/-- One cutoff is chosen before every original real potential on a norm ball;
the resulting actual central projection has a homotopy-invariant finite rank. -/
theorem source_uniform_central_projection (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖ ≤ R →
      q.val = q.val.conjugate →
      IsIdempotentElem (sourceCentralProjection r hr R N q) ∧
      FiniteDimensional ℂ (sourceCentralProjection r hr R N q).range ∧
      Module.finrank ℂ (sourceCentralProjection r hr R N q).range =
        Module.finrank ℂ (sourceCentralProjection r hr R N 0).range := by
  obtain ⟨N,hN,hcut⟩ := exists_wideEndpointHill_cutoff r hr.2 R
  refine ⟨N,hN,fun q hq hreal => ?_⟩
  exact ⟨isIdempotentElem_sourceCentralProjection r hr R N hN (hcut N le_rfl) q hq hreal,
    finiteDimensional_sourceCentralProjection_range r hr R N hN (hcut N le_rfl) q hq hreal,
    sourceCentralProjection_rank_eq_zero r hr R N hN (hcut N le_rfl) q hq hreal⟩

end NLS.Articles.KdVPseudomeasures
