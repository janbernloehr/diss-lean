import NLS.KdV.HillAbelianDiscriminantVariation
import NLS.KdV.HillCompletePhaseFunctionalSeries
import NLS.KdV.HillEnergyDirichletInterpolation

/-! The actual complete local Abelian phase has fixed-energy
Gardner bracket equal to one half of its actual normalized Hill
numerator. Entire energy continuity fills every divisor resonance. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.LpSequence NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV.HillPhysicalOnIndexPhaseChart
variable {P : HillProductEquationPatch} {n : ℕ+}

theorem completePhase_discriminant_Gardner_of_frequency_ne
    (C : HillPhysicalOnIndexPhaseChart P n) (q : PeriodOneHminusOne)
    (hq : q ∈ C.source) (hr : IsRealPeriodOneHminusOne q) (w : ℂ)
    (hw : auxiliaryPeriodOneCharacteristic (by norm_num) (by norm_num) .dirichlet (P.sourcePsi q) w ≠ 0) :
    NLS.Poisson.hminusGardnerBracket C.completePhase
      (fun p => hillHminusDiscriminant p (w^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ))) q =
      (1/2:ℂ)*hillHminusCanonicalPsi n (w^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ),q) := by
  let E := w^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ)
  let V : ℕ+ → PeriodOneHminusOne → ℂ := fun m p => hillHminusDiscriminantDirichletVelocity m (E,p)
  have hc := real_mem_hillHminusOffIndexAnalyticDomain q hr
  have hphys := hillHminusOffIndexAnalyticDomain_subset_physical hc
  have ht := C.tendsto_completePhase_functional_series (fun p => hillHminusDiscriminant p E) q hq hc V
    (C.phase_discriminant_Gardner E q hq)
    (fun m hmn => hillHminusPhysicalOffIndexAbelianValue_discriminant_Gardner n m hmn E q hphys)
  have he : (fun N : ℕ => ∑ j ∈ Finset.Icc (-(N:ℤ)) N,
      positiveScalarExtension (fun m : ℕ+ => hillHminusCanonicalPsi n
        (hillHminusCanonicalDirichlet m q,q)*V m q) j) =ᶠ[atTop]
      (fun N : ℕ => hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet n q,q)*V n q+
        ∑ j ∈ Finset.Icc (-(N:ℤ)) N, positiveScalarExtension (hillHminusOffIndexVelocityTerm n V q) j) := by
    filter_upwards [eventually_ge_atTop (n:ℕ)] with N hN
    exact sum_positive_symmetricCutoff_reinsert_diagonal
      (fun m : ℕ+ => hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet m q,q)*V m q) n N hN
  have hu := (P.tendstoUniformlyOn_Hill_Dirichlet_interpolation n q (C.subset hq).1 hr
    {w} isCompact_singleton (fun z hz => by rcases mem_singleton_iff.mp hz with rfl; exact hw)).tendsto_at
      (mem_singleton w)
  have hterm (j : ℤ) : positiveScalarExtension (fun m : ℕ+ => hillHminusCanonicalPsi n
      (hillHminusCanonicalDirichlet m q,q)*V m q) j =
      (1/2:ℂ)*positiveScalarExtension (fun m : ℕ+ => hillHminusPsiDirichletInterpolationTerm n m q E) j := by
    rw [← positiveScalarExtension_const_mul]
    apply congrArg (fun f : ℕ+ → ℂ => positiveScalarExtension f j)
    funext m
    dsimp only [V,hillHminusDiscriminantDirichletVelocity,hillHminusPsiDirichletInterpolationTerm]
    ring
  have hu' := hu.const_mul (1/2:ℂ)
  have hsum (N : ℕ) : (∑ j ∈ Finset.Icc (-(N:ℤ)) N, positiveScalarExtension
      (fun m : ℕ+ => hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet m q,q)*V m q) j) =
      (1/2:ℂ)*∑ j ∈ Finset.Icc (-(N:ℤ)) N, positiveScalarExtension
        (fun m : ℕ+ => hillHminusPsiDirichletInterpolationTerm n m q E) j := by
    simp only [hterm,Finset.mul_sum]
  have hv := hu'.congr' (Eventually.of_forall (fun N => (hsum N).symm))
  exact tendsto_nhds_unique ht (hv.congr' he)

theorem completePhase_discriminant_Gardner_of_real
    (C : HillPhysicalOnIndexPhaseChart P n) (E : ℂ) (q : PeriodOneHminusOne)
    (hq : q ∈ C.source) (hr : IsRealPeriodOneHminusOne q) :
    NLS.Poisson.hminusGardnerBracket C.completePhase (fun p => hillHminusDiscriminant p E) q =
      (1/2:ℂ)*hillHminusCanonicalPsi n (E,q) := by
  let c : ℂ := P.parent.parent.miuraBall.actionBall.shift
  let u := P.parent.parent.miuraBall.actionBall.lift q
  let L := NLS.Poisson.gardnerCotangentBivector (fderiv ℂ C.completePhase q)
  have hleft : Continuous (fun w : ℂ => NLS.Poisson.hminusGardnerBracket C.completePhase
      (fun p => hillHminusDiscriminant p (w^2-c)) q) :=
    L.continuous.comp ((analyticOnNhd_hillHminusDiscriminantCotangent_energy q).continuous.comp
      (continuous_id.pow 2 |>.sub continuous_const))
  have hright : Continuous (fun w : ℂ => (1/2:ℂ)*hillHminusCanonicalPsi n (w^2-c,q)) :=
    continuous_const.mul ((show AnalyticOnNhd ℂ (fun w : ℂ => hillHminusCanonicalPsi n (w^2-c,q)) univ from by
      intro w _
      exact (analyticOnNhd_hillHminusCanonicalPsi n (w^2-c,q) ⟨mem_univ _,C.source_subset_psi hq⟩).comp
        (f := fun z : ℂ => (z^2-c,q)) (((analyticAt_id.pow 2).sub analyticAt_const).prod analyticAt_const)).continuous)
  have he := Continuous.ext_on (s := (range (hillMiuraDiracDirichlet u))ᶜ)
    ((countable_range (hillMiuraDiracDirichlet u)).dense_compl ℂ) hleft hright (fun w hw => ?_)
  · have hs : (Complex.sqrt (E+c))^2-c=E := by rw [complex_sqrt_sq]; ring
    simpa only [hs] using congrFun he (Complex.sqrt (E+c))
  · exact C.completePhase_discriminant_Gardner_of_frequency_ne q hq hr w (by
      intro hz
      exact hw ((mem_range_hillMiuraDiracDirichlet_iff u w).mpr hz))

theorem exists_local_completePhase_discriminant_Gardner
    (C : HillPhysicalOnIndexPhaseChart P n) (q : PeriodOneHminusOne)
    (hq : q ∈ C.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ r : ℝ, 0 < r ∧ ball q r ⊆ C.source ∩ hillHminusOffIndexAnalyticDomain ∧
      AnalyticOnNhd ℂ C.completePhase (ball q r) ∧
      ∀ E : ℂ, ∀ p ∈ ball q r,
        NLS.Poisson.hminusGardnerBracket C.completePhase (fun b => hillHminusDiscriminant b E) p =
          (1/2:ℂ)*hillHminusCanonicalPsi n (E,p) := by
  obtain ⟨r,hrpos,hsub⟩ := Metric.mem_nhds_iff.mp
    ((C.source_open.inter isOpen_hillHminusOffIndexAnalyticDomain).mem_nhds
      ⟨hq,real_mem_hillHminusOffIndexAnalyticDomain q hr⟩)
  have hphase := C.analytic_completePhase.mono hsub
  refine ⟨r,hrpos,hsub,hphase,?_⟩
  intro E
  apply analytic_eqOn_of_real_periodOneHminus (ball q r) isOpen_ball
    (convex_ball q r).isPreconnected ⟨q,mem_ball_self hrpos,hr⟩ _ _
    (NLS.Poisson.analyticOnNhd_hminusGardnerBracket _ _ hphase
      ((analyticOnNhd_hillHminusDiscriminant_source E).mono (subset_univ _)))
    (analyticOnNhd_const.mul (show AnalyticOnNhd ℂ (fun p => hillHminusCanonicalPsi n (E,p)) (ball q r) from by
      intro p hp
      exact (analyticOnNhd_hillHminusCanonicalPsi n (E,p) ⟨mem_univ _,C.source_subset_psi (hsub hp).1⟩).comp
        (f := fun b : PeriodOneHminusOne => (E,b)) (analyticAt_const.prod analyticAt_id)))
  intro p hp hpr
  exact C.completePhase_discriminant_Gardner_of_real E p (hsub hp).1 hpr

end NLS.KdV.HillPhysicalOnIndexPhaseChart
