import NLS.ZakharovShabat.SourceSpectralDisplacementSobolevBall
import NLS.ZakharovShabat.SourceBoundaryAntiFourierAnalytic
import NLS.ZakharovShabat.SobolevSourceRealSmoothApproximation

/-! # Complete anti-discriminant Fourier bounds on Sobolev balls

The actual boundary anti-discriminant Fourier remainders have uniform one-order stronger bounds on every real positive-integer Sobolev ball.
-/

noncomputable section
open Set Metric Filter Topology Complex NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The anti-discriminant Fourier error in original L2 coordinates. -/
def sourceBoundaryAntiFourierL2Error (θ : BoundaryCondition) (n : ℤ) (φ : CoeffPair 2) : ℂ :=
  sourceAntiDiscriminantCandidate (by norm_num) (by norm_num) φ
    (canonicalPeriodOneBoundaryRoots (by norm_num) (by norm_num) θ φ n)+
    I*exp (I*((Real.pi:ℂ)*n))*φ.snd n-I*exp (-I*((Real.pi:ℂ)*n))*φ.fst (-n)

@[simp] theorem sourceBoundaryAntiFourierL2Error_higherSobolev
    (s : ℕ) (θ : BoundaryCondition) (n : ℤ) (ab : SobolevSource s) :
    sourceBoundaryAntiFourierL2Error θ n (higherSobolevSourceInclusion s ab) =
      sourceBoundaryAntiFourierError s θ n ab := by
  simp only [sourceBoundaryAntiFourierL2Error,sourceBoundaryAntiFourierError,
    higherSobolevSourceInclusion_fst,higherSobolevSourceInclusion_snd]

/-- The literal anti-discriminant Fourier coordinate is continuous at real
sources in the original L2 norm. -/
theorem continuousAt_sourceBoundaryAntiFourierL2Error_of_real
    (φ : realTypeSourceLocus 2) (θ : BoundaryCondition) (n : ℤ) :
    ContinuousAt (sourceBoundaryAntiFourierL2Error θ n) φ.val := by
  obtain ⟨U,_,hφU,hμ⟩ := exists_local_source_allBoundaryRoots_analytic
    (p := 2) (by norm_num) (by norm_num) φ.val φ.property
  have hAc : Continuous (fun q : ℂ × NLS.CoeffPair 2 =>
      sourceAntiDiscriminantCandidate (by norm_num) (by norm_num) q.2 q.1) :=
    continuousOn_univ.mp (analyticOnNhd_sourceAntiDiscriminantCandidate_joint (p := 2)
      (by norm_num) (by norm_num)).continuousOn
  have ha : ContinuousAt (fun ψ : CoeffPair 2 => sourceAntiDiscriminantCandidate
      (by norm_num) (by norm_num) ψ
      (canonicalPeriodOneBoundaryRoots (by norm_num) (by norm_num) θ ψ n)) φ.val :=
    ContinuousAt.comp
      (g := fun q : ℂ × NLS.CoeffPair 2 => sourceAntiDiscriminantCandidate
        (by norm_num) (by norm_num) q.2 q.1)
      (f := fun ψ : CoeffPair 2 =>
        (canonicalPeriodOneBoundaryRoots (by norm_num) (by norm_num) θ ψ n,ψ))
      hAc.continuousAt ((hμ θ n φ.val hφU).continuousAt.prodMk continuousAt_id)
  have hfst : ContinuousAt (fun ψ : CoeffPair 2 => ψ.fst (-n)) φ.val :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (-n)).continuous.continuousAt.comp
      (CoeffPair.toMax 2).continuous.continuousAt.fst
  have hsnd : ContinuousAt (fun ψ : CoeffPair 2 => ψ.snd n) φ.val :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).continuous.continuousAt.comp
      (CoeffPair.toMax 2).continuous.continuousAt.snd
  exact (ha.add (continuousAt_const.mul hsnd)).sub (continuousAt_const.mul hfst)

/-- A common cutoff and bound control both canonical boundary anti-discriminant
Fourier tails on an entire real Hs ball, for matching smooth representatives. -/
theorem exists_uniform_real_source_boundary_anti_smooth_fourier_tail_bound
    (s : ℕ) (hs : 1 ≤ s) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ ab : realTypeHigherSobolevSourceLocus s, ‖ab.val‖ ≤ R → ∀ θ : BoundaryCondition,
      ∀ a b : ℝ → ℂ, ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.val.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.val.2.val j = periodOneCoefficient b j) →
      ∃ f : ScalarSobolev (s+1),
        (∀ n, f.val n = if K ≤ n.natAbs then sourceBoundaryAntiFourierError s θ n ab.val else 0) ∧ ‖f‖ ≤ C := by
  obtain ⟨D,M,hD,hM,hdisp⟩ := exists_uniform_real_higherSobolev_displacement_envelopes s hs R hR
  obtain ⟨K,hK,C,hC,h⟩ := exists_uniform_boundary_anti_fourier_tail_bound s hs R D M hR hD hM
  refine ⟨K,hK,C,hC,?_⟩
  intro ab hab θ a b ha hb hpa hpb hca hcb
  obtain ⟨habD,habM⟩ := (hdisp ab hab).1 θ
  let δ₂ := sourceBoundaryDisplacement (by norm_num) (by norm_num) θ (higherSobolevSourceInclusion s ab.val)
  let δ : NLS.Coeff ⊤ := Coeff.exponentInclusion (by simp : (2:ℝ≥0∞) ≤ ⊤) δ₂
  have hδD : ‖δ‖ ≤ D := (Coeff.norm_exponentInclusion_le _ δ₂).trans habD
  have hδM (n : ℤ) : (1+|(n:ℝ)|)*‖δ n‖ ≤ M := by
    simpa only [δ,Coeff.exponentInclusion_apply] using habM n
  have hν (n : ℤ) : (Real.pi:ℂ)*n+δ n =
      canonicalPeriodOneBoundaryRoots (by norm_num) (by norm_num) θ (higherSobolevSourceInclusion s ab.val) n := by
    simp only [δ,Coeff.exponentInclusion_apply,δ₂,sourceBoundaryDisplacement_apply]
    ring
  have hroot (n : ℤ) (_ : K ≤ n.natAbs) : classicalSeparatedCharacteristic θ
      (classicalPotentialOfFunctions a b ha.continuous hb.continuous) ((Real.pi:ℂ)*n+δ n) = 0 := by
    rw [hν n]
    exact classicalSeparatedCharacteristic_higherSobolev_canonicalRoot_eq_zero s hs ab.val a b
      ha.continuous hb.continuous hpa hpb hca hcb θ n
  obtain ⟨f,hf,hfn⟩ := h K le_rfl ab.val hab a b ha hb hpa hpb hca hcb δ hδD hδM θ hroot
  refine ⟨f,?_,hfn⟩
  intro n
  rw [hf n]
  split_ifs with hn
  · rw [hν n,← (higherSobolev_spectral_functions_eq_classical s hs ab.val a b ha.continuous hb.continuous hpa hpb hca hcb _).2.1]
    rfl
  · rfl

/-- Symmetric smooth approximation extends the uniform tail to every real
source in the ball, for both boundary conditions. -/
theorem exists_uniform_real_sourceBoundaryAntiFourierError_tail_bound
    (s : ℕ) (hs : 1 ≤ s) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ ab : realTypeHigherSobolevSourceLocus s, ‖ab.val‖ ≤ R → ∀ θ : BoundaryCondition,
      ∃ f : ScalarSobolev (s+1),
        (∀ n, f.val n = if K ≤ n.natAbs then sourceBoundaryAntiFourierError s θ n ab.val else 0) ∧ ‖f‖ ≤ C := by
  classical
  obtain ⟨K,hK,C,hC,hbound⟩ := exists_uniform_real_source_boundary_anti_smooth_fourier_tail_bound s hs R hR
  refine ⟨K,hK,C,hC,?_⟩
  intro ab hab θ
  let u (N : ℕ) : realTypeHigherSobolevSourceLocus s :=
    ⟨sobolevSourceSymmetricTruncate s N ab.val,sobolevSourceSymmetricTruncate_real s N ab⟩
  have he (N : ℕ) : ∃ e : ScalarSobolev (s+1),
      (∀ n, e.val n = if K ≤ n.natAbs then sourceBoundaryAntiFourierError s θ n (u N).val else 0) ∧ ‖e‖ ≤ C := by
    obtain ⟨a,b,ha,hb,hpa,hpb,hca,hcb⟩ := sobolevSourceSymmetricTruncate_smooth s N ab.val
    exact hbound (u N) ((norm_sobolevSourceSymmetricTruncate_le s N ab.val).trans hab)
      θ a b ha hb hpa hpb hca hcb
  choose e he hen using he
  refine WeightedCoeff.exists_of_bounded_coefficientwise_tendsto (l := (atTop : Filter ℕ))
    (Weight.sobolev ((s+1:ℕ):ℝ)) e _ C hen ?_
  intro n
  simp only [he]
  by_cases hn : K ≤ n.natAbs
  · simp only [if_pos hn]
    have ht := Filter.Tendsto.comp
      (continuousAt_sourceBoundaryAntiFourierL2Error_of_real
        ⟨higherSobolevSourceInclusion s ab.val,ab.property⟩ θ n)
      (((higherSobolevSourceInclusion s).continuous.tendsto ab.val).comp
        (tendsto_sobolevSourceSymmetricTruncate s ab.val))
    simpa only [Function.comp_def,u,sourceBoundaryAntiFourierL2Error_higherSobolev] using ht
  · simp only [if_neg hn]
    exact tendsto_const_nhds

/-- The complete anti-discriminant Fourier remainder is uniformly bounded
in h^(s+1) on each real original Hs ball, including all central indices. -/
theorem exists_uniform_real_sourceBoundaryAntiFourierRemainder_bound
    (s : ℕ) (hs : 1 ≤ s) (R : ℝ) (hR : 0 ≤ R) (θ : BoundaryCondition) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : realTypeHigherSobolevSourceLocus s, ‖ab.val‖ ≤ R →
      ‖sourceBoundaryAntiFourierRemainder s θ ab.val‖ ≤ C ∧
      ∀ n, (sourceBoundaryAntiFourierRemainder s θ ab.val).val n =
        sourceBoundaryAntiFourierError s θ n ab.val := by
  classical
  obtain ⟨N,_,C,hC,htail⟩ := exists_uniform_real_sourceBoundaryAntiFourierError_tail_bound s hs R hR
  let J := higherSobolevSourceInclusion s
  let X := closedBall (0 : SobolevSource s) R ∩ (J ⁻¹' realTypeSourceLocus 2)
  let K := closure (J '' X)
  obtain ⟨hK,hKreal⟩ := higherSobolev_real_ball_image_compact s hs R
  let H (φ : CoeffPair 2) : ScalarSobolev (s+1) := WeightedCoeff.finiteBlock
    (Weight.sobolev ((s+1:ℕ):ℝ)) (Coeff.lowFrequencies N) (fun n => sourceBoundaryAntiFourierL2Error θ n φ)
  have hH : ContinuousOn H K := by
    intro φ hφ
    exact (WeightedCoeff.continuousAt_finiteBlock _ _ _ φ
      (fun n _ => continuousAt_sourceBoundaryAntiFourierL2Error_of_real ⟨φ,hKreal hφ⟩ θ n)).continuousWithinAt
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hH
  refine ⟨C+max B 0,by positivity,?_⟩
  intro ab hab
  have hmem : J ab.val ∈ K := subset_closure ⟨ab.val,
    ⟨by simpa only [mem_closedBall,dist_zero_right] using hab,ab.property⟩,rfl⟩
  obtain ⟨e,he,hen⟩ := htail ab hab θ
  have hval (n : ℤ) : (e+H (J ab.val)).val n = sourceBoundaryAntiFourierError s θ n ab.val := by
    simp only [WeightedCoeff.add_val,he,H,WeightedCoeff.finiteBlock_val,Coeff.mem_lowFrequencies,J,
      sourceBoundaryAntiFourierL2Error_higherSobolev]
    by_cases hn : N ≤ n.natAbs
    · simp only [if_pos hn,if_neg (not_lt_of_ge hn),add_zero]
    · simp only [if_neg hn,if_pos (Nat.lt_of_not_ge hn),zero_add]
  have heq : sourceBoundaryAntiFourierRemainder s θ ab.val = e+H (J ab.val) := by
    apply WeightedCoeff.ofFunctionOrZero_eq_of_coordinates
    exact hval
  rw [heq]
  exact ⟨(norm_add_le _ _).trans (add_le_add hen ((hB (J ab.val) hmem).trans (le_max_left _ _))),hval⟩

end NLS.ZakharovShabat
