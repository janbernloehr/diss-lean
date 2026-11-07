import NLS.KdV.HillAuxiliaryDirichletSlope
import NLS.KdV.HillPhysicalDirichletSheetCoefficient
import NLS.KdV.HillDirichletFilledQuotient
import NLS.ComplexAnalysis.QuadraticSimplePolePair
import NLS.SequenceSpaces.SymmetricPositiveCutoff

/-! Exact pairing of the ACTUAL auxiliary signed interpolation
terms into the original Hill energy residues, with the analytic
filled Dirichlet quotient retained. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis NLS.LpSequence
open scoped ENNReal
namespace NLS.KdV

def hillHminusPsiDirichletInterpolationTerm (n m : ℕ+) (q : PeriodOneHminusOne) (E : ℂ) : ℂ :=
  hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet m q,q)*
    hillHminusDirichletFilledQuotient m (E,q)/
      deriv (hillHminusDirichlet q) (hillHminusCanonicalDirichlet m q)

theorem analyticOnNhd_hillHminusPsiDirichletInterpolationTerm (n m : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ hillHminusCanonicalDirichletDomain) :
    AnalyticOnNhd ℂ (hillHminusPsiDirichletInterpolationTerm n m q) univ := by
  intro E _
  exact (analyticAt_const.mul ((analyticOnNhd_hillHminusDirichletFilledQuotient m (E,q)
    ⟨mem_univ _,hq⟩).comp (f := fun z : ℂ => (z,q)) (analyticAt_id.prod analyticAt_const))).div_const

theorem HillProductEquationPatch.weighted_auxiliary_interpolation_pair
    (P : HillProductEquationPatch) (n m : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ P.source)
    (hr : IsRealPeriodOneHminusOne q) (w : ℂ)
    (hw : auxiliaryPeriodOneCharacteristic (by norm_num) (by norm_num) .dirichlet (P.sourcePsi q) w ≠ 0) :
    (hillHminusDirichlet q (w^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ))/2)*
      ((hillAuxiliaryPsiInterpolationTerm ((n:ℕ):ℤ)
          (P.parent.family.roots ((n:ℕ):ℤ) (P.sourcePsi q):Coeff 2)
          (P.parent.parent.miuraBall.actionBall.lift q) ((m:ℕ):ℤ) w+
        hillAuxiliaryPsiInterpolationTerm ((n:ℕ):ℤ)
          (P.parent.family.roots ((n:ℕ):ℤ) (P.sourcePsi q):Coeff 2)
          (P.parent.parent.miuraBall.actionBall.lift q) ((m:ℕ):ℤ) (-w))+
       (hillAuxiliaryPsiInterpolationTerm ((n:ℕ):ℤ)
          (P.parent.family.roots ((n:ℕ):ℤ) (P.sourcePsi q):Coeff 2)
          (P.parent.parent.miuraBall.actionBall.lift q) (-((m:ℕ):ℤ)) w+
        hillAuxiliaryPsiInterpolationTerm ((n:ℕ):ℤ)
          (P.parent.family.roots ((n:ℕ):ℤ) (P.sourcePsi q):Coeff 2)
          (P.parent.parent.miuraBall.actionBall.lift q) (-((m:ℕ):ℤ)) (-w))) =
      hillHminusPsiDirichletInterpolationTerm n m q (w^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ)) := by
  let u : PeriodOneRealL2 := ⟨P.parent.parent.miuraBall.actionBall.lift q,
    P.parent.parent.miuraBall.actionBall.lift_real q (P.parent.subset (P.subset hq)).1 hr⟩
  let c : ℂ := P.parent.parent.miuraBall.actionBall.shift
  let μ := hillMiuraDiracDirichlet u.val ((m:ℕ):ℤ)
  let a : Coeff 2 := P.parent.family.roots ((n:ℕ):ℤ) (P.sourcePsi q)
  let g := auxiliaryPeriodOneCharacteristic (by norm_num) (by norm_num) .dirichlet (hillMiuraDiagonal u.val)
  let d := deriv (hillHminusDirichlet q) (hillHminusCanonicalDirichlet m q)
  let E := w^2-c
  have hμpos : 0 < μ.re := (hillMiuraDiracDirichlet_re_pos_iff u ((m:ℕ):ℤ)).mpr (by exact_mod_cast m.pos)
  have hμ : μ ≠ 0 := by intro he; rw [he] at hμpos; exact lt_irrefl _ hμpos
  have hd : d ≠ 0 := deriv_hillHminusCanonicalDirichlet_ne_zero m q (P.source_subset_canonicalDirichlet hq)
  have henergy : μ^2-c = hillHminusCanonicalDirichlet m q := P.physicalDirichletFrequency_energy m q hq
  have hS : hillHminusDirichlet q (μ^2-c) = 0 := by
    rw [henergy]
    exact hillHminusCanonicalDirichlet_is_root m q (P.source_subset_canonicalDirichlet hq)
  have himage := P.parent.parent.miuraBall.actionBall.image q (P.parent.subset (P.subset hq)).1
  have hdp : deriv g μ = 2*μ^2*d := by
    have hh := deriv_auxiliaryDirichlet_at_Hill_root q u.val c μ himage hS
    rw [henergy] at hh
    exact hh
  have hdn : deriv g (-μ) = 2*μ^2*d := by
    have hh := deriv_auxiliaryDirichlet_at_Hill_root q u.val c (-μ) himage (by simpa only [neg_sq] using hS)
    simpa only [neg_sq,henergy] using hh
  have hgμ : g μ = 0 := (mem_range_hillMiuraDiracDirichlet_iff u.val μ).mp ⟨((m:ℕ):ℤ),rfl⟩
  have hgn : g (-μ) = 0 := by
    calc
      g (-μ) = -g μ := auxiliaryDirichlet_hillMiuraDiagonal_neg u.val μ
      _ = 0 := by rw [hgμ,neg_zero]
  have hwp : w ≠ μ := by intro he; apply hw; change g w=0; rw [he,hgμ]
  have hwn : w ≠ -μ := by intro he; apply hw; change g w=0; rw [he,hgn]
  have hE : E ≠ hillHminusCanonicalDirichlet m q := by
    intro he
    have hs : w^2=μ^2 := by dsimp only [E] at he; linear_combination he-henergy
    rcases eq_or_eq_neg_of_sq_eq_sq w μ hs with heq | heq
    · exact hwp heq
    · exact hwn heq
  have hnum : sourcePsiCandidate ((n:ℕ):ℤ) (μ,a)-sourcePsiCandidate ((n:ℕ):ℤ) (-μ,a) =
      2*μ*hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet m q,q) := by
    have hh := P.canonicalPsi_frequency_identity n q hq μ
    rw [henergy] at hh
    exact hh.symm
  have hpair := weighted_opposite_simple_pole_pairs
    (sourcePsiCandidate ((n:ℕ):ℤ) (μ,a)) (sourcePsiCandidate ((n:ℕ):ℤ) (-μ,a)) μ d w
    (hillHminusDirichlet q E) (hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet m q,q)) hμ hd hwp hwn hnum
  have hden : E-hillHminusCanonicalDirichlet m q=w^2-μ^2 := by dsimp only [E]; linear_combination henergy
  dsimp only [hillAuxiliaryPsiInterpolationTerm]
  rw [hillMiuraDiracDirichlet_neg u ((m:ℕ):ℤ)]
  change (hillHminusDirichlet q E/2)*
    ((sourcePsiCandidate ((n:ℕ):ℤ) (μ,a)/deriv g μ/(w-μ)+
      sourcePsiCandidate ((n:ℕ):ℤ) (μ,a)/deriv g μ/(-w-μ))+
     (sourcePsiCandidate ((n:ℕ):ℤ) (-μ,a)/deriv g (-μ)/(w-(-μ))+
      sourcePsiCandidate ((n:ℕ):ℤ) (-μ,a)/deriv g (-μ)/(-w-(-μ)))) = _
  rw [hdp,hdn]
  simp only [sub_neg_eq_add]
  rw [hpair]
  rw [hillHminusPsiDirichletInterpolationTerm,hillHminusDirichletFilledQuotient_off_root m q
    (P.source_subset_canonicalDirichlet hq) E hE,hden]
  dsimp only [d]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

end NLS.KdV
