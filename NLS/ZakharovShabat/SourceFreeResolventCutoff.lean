import NLS.ZakharovShabat.SourceFreeResolvent
import Mathlib.Analysis.Normed.Operator.Prod

/-! # The finite-rank proof of Lemma 3.2(i)

The actual signed Fourier series converges in the original finite-p pair norm.
Explicit Fourier cutoffs have finite-dimensional range and converge in operator
norm, giving the closure argument printed on p.24. In particular this applies
to the original l1 space in the statement.
-/

noncomputable section
open scoped ENNReal
open Filter
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The first raw Fourier component uses the plus denominator. -/
@[simp] theorem sourceFreeResolvent_fst_apply (hp : p ≠ ⊤) (z : ℂ) (hz : z ∉ freeLattice)
    (a : CoeffPair p) (n : ℤ) :
    (sourceFreeResolvent hp z hz a).fst n = a.fst n/(z+(Real.pi : ℂ)*n) :=
  freeResolvent_fst_apply z hz _ n

/-- The second raw Fourier component uses the minus denominator. -/
@[simp] theorem sourceFreeResolvent_snd_apply (hp : p ≠ ⊤) (z : ℂ) (hz : z ∉ freeLattice)
    (a : CoeffPair p) (n : ℤ) :
    (sourceFreeResolvent hp z hz a).snd n = a.snd n/(z-(Real.pi : ℂ)*n) :=
  freeResolvent_snd_apply z hz _ n

/-- The literal signed Fourier expansion converges in the original pair norm. -/
theorem hasSum_sourceFreeResolvent_signed (hp : p ≠ ⊤) (z : ℂ) (hz : z ∉ freeLattice)
    (a : CoeffPair p) :
    HasSum (fun m : ℤ => (CoeffPair.toMax p).symm
      (lp.single p (-m) (a.fst (-m)/(z-(Real.pi : ℂ)*m)),
        lp.single p m (a.snd m/(z-(Real.pi : ℂ)*m))))
      (sourceFreeResolvent hp z hz a) := by
  have hfirst := (Equiv.neg ℤ).hasSum_iff.mpr
    (lp.hasSum_single hp (sourceFreeResolvent hp z hz a).fst)
  have hpair := hfirst.prodMk (lp.hasSum_single hp (sourceFreeResolvent hp z hz a).snd)
  have h := (CoeffPair.toMax p).symm.toContinuousLinearMap.hasSum hpair
  change HasSum _ ((CoeffPair.toMax p).symm
    ((CoeffPair.toMax p) (sourceFreeResolvent hp z hz a))) at h
  rw [ContinuousLinearEquiv.symm_apply_apply] at h
  simpa only [Function.comp_apply,Equiv.neg_apply,sourceFreeResolvent_fst_apply,sourceFreeResolvent_snd_apply,
    Int.cast_neg,mul_neg,← sub_eq_add_neg,ContinuousLinearEquiv.coe_coe,
    CoeffPair.toMax_symm_apply] using h

/-- Explicit finite Fourier approximants in the original source norm. -/
def sourceFreeResolventCutoff (_hp : p ≠ ⊤) (z : ℂ) (hz : z ∉ freeLattice)
    (s : Finset ℤ) : CoeffPair p →L[ℂ] CoeffPair p :=
  (CoeffPair.toMax p).symm.conjContinuousAlgEquiv
    ((-((Coeff.truncateCLM s).comp (scalarResolvent (p := p) (-z) (neg_notMem_freeLattice hz)))).prodMap
      ((Coeff.truncateCLM s).comp (scalarResolvent z hz)))

theorem sourceFreeResolventCutoff_fst (hp : p ≠ ⊤) (z : ℂ) (hz : z ∉ freeLattice)
    (s : Finset ℤ) (a : CoeffPair p) (n : ℤ) :
    (sourceFreeResolventCutoff hp z hz s a).fst n =
      if n ∈ s then a.fst n/(z+(Real.pi : ℂ)*n) else 0 := by
  change -(Coeff.truncate s (scalarResolvent (-z) (neg_notMem_freeLattice hz) a.fst) n) = _
  rw [Coeff.truncate_apply]
  by_cases hn : n ∈ s
  · simp only [hn,if_true,scalarResolvent_apply]
    rw [show -z-(Real.pi : ℂ)*n = -(z+(Real.pi : ℂ)*n) by ring,div_neg,neg_neg]
  · simp [hn]

theorem sourceFreeResolventCutoff_snd (hp : p ≠ ⊤) (z : ℂ) (hz : z ∉ freeLattice)
    (s : Finset ℤ) (a : CoeffPair p) (n : ℤ) :
    (sourceFreeResolventCutoff hp z hz s a).snd n =
      if n ∈ s then a.snd n/(z-(Real.pi : ℂ)*n) else 0 := by
  change Coeff.truncate s (scalarResolvent z hz a.snd) n = _
  rw [Coeff.truncate_apply,scalarResolvent_apply]

/-- Recording the retained coefficients in both components. -/
private def cutoffCoordinates (hp : p ≠ ⊤) (z : ℂ) (hz : z ∉ freeLattice)
    (s : Finset ℤ) : (sourceFreeResolventCutoff hp z hz s).range →ₗ[ℂ] ((s → ℂ) × (s → ℂ)) :=
  { toFun := fun x => (fun n => x.val.fst n, fun n => x.val.snd n)
    map_add' := by intro x y; rfl
    map_smul' := by intro c x; rfl }

private theorem cutoffCoordinates_injective (hp : p ≠ ⊤) (z : ℂ) (hz : z ∉ freeLattice)
    (s : Finset ℤ) : Function.Injective (cutoffCoordinates hp z hz s) := by
  let A := sourceFreeResolventCutoff hp z hz s
  have hout (x : A.range) (n : ℤ) (hn : n ∉ s) : x.val.fst n = 0 ∧ x.val.snd n = 0 := by
    obtain ⟨a,ha⟩ := x.property
    change A a = x.val at ha
    rw [← ha]
    simp [A,sourceFreeResolventCutoff_fst,sourceFreeResolventCutoff_snd,hn]
  intro x y hxy
  apply Subtype.ext
  apply (CoeffPair.toMax p).injective
  apply Prod.ext <;> ext n
  · change x.val.fst n = y.val.fst n
    by_cases hn : n ∈ s
    · exact congrFun (congrArg Prod.fst hxy) ⟨n,hn⟩
    · rw [(hout x n hn).1,(hout y n hn).1]
  · change x.val.snd n = y.val.snd n
    by_cases hn : n ∈ s
    · exact congrFun (congrArg Prod.snd hxy) ⟨n,hn⟩
    · rw [(hout x n hn).2,(hout y n hn).2]

/-- The range injects into two finite lists of retained coefficients. -/
theorem finiteDimensional_sourceFreeResolventCutoff (hp : p ≠ ⊤)
    (z : ℂ) (hz : z ∉ freeLattice) (s : Finset ℤ) :
    FiniteDimensional ℂ (sourceFreeResolventCutoff hp z hz s).range :=
  FiniteDimensional.of_injective (cutoffCoordinates hp z hz s) (cutoffCoordinates_injective hp z hz s)

/-- Each cutoff has rank at most twice the number of retained raw frequencies. -/
theorem finrank_sourceFreeResolventCutoff_le (hp : p ≠ ⊤)
    (z : ℂ) (hz : z ∉ freeLattice) (s : Finset ℤ) :
    Module.finrank ℂ (sourceFreeResolventCutoff hp z hz s).range ≤ 2*s.card := by
  classical
  calc
    _ ≤ Module.finrank ℂ ((s → ℂ) × (s → ℂ)) :=
      LinearMap.finrank_le_finrank_of_injective (cutoffCoordinates_injective hp z hz s)
    _ = 2*s.card := by simp [Module.finrank_prod, two_mul]

/-- These finite-rank approximants converge in the original operator norm. -/
theorem tendsto_sourceFreeResolventCutoff (hp : p ≠ ⊤)
    (z : ℂ) (hz : z ∉ freeLattice) :
    Tendsto (sourceFreeResolventCutoff hp z hz) atTop (nhds (sourceFreeResolvent hp z hz)) := by
  have hA := (tendsto_scalarResolvent_cutoff (p := p) (-z) (neg_notMem_freeLattice hz)).neg
  have hB := tendsto_scalarResolvent_cutoff (p := p) z hz
  have hpair := (ContinuousLinearMap.prodMapL ℂ (Coeff p) (Coeff p) (Coeff p) (Coeff p)).continuous.continuousAt.tendsto.comp
    (hA.prodMk_nhds hB)
  have h := (CoeffPair.toMax p).symm.conjContinuousAlgEquiv.continuous.continuousAt.tendsto.comp hpair
  convert h using 1
  · rfl
  · rw [sourceFreeResolvent,freeResolvent_eq_prodMap]
    rfl

/-- Finite-dimensional cutoff ranges give compact approximants. -/
theorem isCompactOperator_sourceFreeResolventCutoff (hp : p ≠ ⊤)
    (z : ℂ) (hz : z ∉ freeLattice) (s : Finset ℤ) :
    IsCompactOperator (sourceFreeResolventCutoff hp z hz s) := by
  let A := sourceFreeResolventCutoff hp z hz s
  let := finiteDimensional_sourceFreeResolventCutoff hp z hz s
  have h := isCompactOperator_of_locallyCompactSpace_dom A.rangeRestrict
  exact h.clm_comp A.range.subtypeL

/-- Compactness follows directly from the original-norm cutoff convergence. -/
theorem isCompactOperator_sourceFreeResolvent_from_cutoffs (hp : p ≠ ⊤)
    (z : ℂ) (hz : z ∉ freeLattice) :
    IsCompactOperator (sourceFreeResolvent hp z hz) :=
  isCompactOperator_of_tendsto (tendsto_sourceFreeResolventCutoff hp z hz)
    (Eventually.of_forall (isCompactOperator_sourceFreeResolventCutoff hp z hz))

/-- Every positive tolerance admits a finite-rank approximation in the original operator norm. -/
theorem exists_sourceFreeResolventCutoff_norm_sub_lt (hp : p ≠ ⊤)
    (z : ℂ) (hz : z ∉ freeLattice) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset ℤ, Module.finrank ℂ (sourceFreeResolventCutoff hp z hz s).range ≤ 2*s.card ∧
      ‖sourceFreeResolventCutoff hp z hz s-sourceFreeResolvent hp z hz‖ < ε := by
  obtain ⟨s,hs⟩ := Metric.tendsto_atTop.mp (tendsto_sourceFreeResolventCutoff hp z hz) ε hε
  exact ⟨s,finrank_sourceFreeResolventCutoff_le hp z hz s,by simpa only [dist_eq_norm] using hs s le_rfl⟩

end NLS.ZakharovShabat
