import NLS.KdV.HillAuxiliaryDirichletSlope
import NLS.ZakharovShabat.SourcePsiCandidateEntireVariation

/-! Full native derivatives of the actual normalized Hill numerator
retain the actual original deleted-root directions under the matched
Miura lift. Quadratic descent gives the exact odd frequency variation. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV.HillProductEquationPatch

def nativePsiRootMap (P : HillProductEquationPatch) (n : ℕ+) (q : PeriodOneHminusOne) : DeletedCoeff 2 ((n:ℕ):ℤ) :=
  P.parent.family.roots ((n:ℕ):ℤ) (P.sourcePsi q)

theorem analytic_nativePsiRootMap (P : HillProductEquationPatch) (n : ℕ+) :
    AnalyticOnNhd ℂ (P.nativePsiRootMap n) P.source := by
  intro q hq
  exact (P.parent.family.verified.analytic ((n:ℕ):ℤ) (P.sourcePsi q)
    (P.parent.subset (P.subset hq)).2).comp (f := P.sourcePsi) (P.analytic_sourcePsi q hq)

def nativePsiRootDirection (P : HillProductEquationPatch) (n : ℕ+) (q h : PeriodOneHminusOne) :
    DeletedCoeff 2 ((n:ℕ):ℤ) := (fderiv ℂ (P.nativePsiRootMap n) q) h

theorem fderiv_nativePsiCandidate_eq_root_variation (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (h : PeriodOneHminusOne) (z : ℂ) :
    (fderiv ℂ (fun p => sourcePsiCandidate ((n:ℕ):ℤ) (z,(P.nativePsiRootMap n p:Coeff 2))) q) h =
      sourcePsiCandidateVariation ((n:ℕ):ℤ) (P.nativePsiRootMap n q:Coeff 2)
        (P.nativePsiRootDirection n q h:Coeff 2) z := by
  let i : DeletedCoeff 2 ((n:ℕ):ℤ) →L[ℂ] Coeff 2 :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 ((n:ℕ):ℤ)).ker.subtypeL
  let N : Coeff 2 → ℂ := fun a => sourcePsiCandidate ((n:ℕ):ℤ) (z,a)
  have hN : DifferentiableAt ℂ N (P.nativePsiRootMap n q:Coeff 2) :=
    ((analyticOnNhd_sourcePsiCandidate (by norm_num) (by norm_num) ((n:ℕ):ℤ)
      (z,(P.nativePsiRootMap n q:Coeff 2)) (mem_univ _)).comp
      (f := fun a : Coeff 2 => (z,a)) (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hA := i.hasFDerivAt.comp q (P.analytic_nativePsiRootMap n q hq).differentiableAt.hasFDerivAt
  have he := congrArg (fun L : PeriodOneHminusOne →L[ℂ] ℂ => L h) (hN.hasFDerivAt.comp q hA).fderiv
  simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,N,i,sourcePsiCandidateVariation,
    nativePsiRootDirection,Submodule.subtypeL_apply] using he

theorem fderiv_canonicalPsi_frequency_identity (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (h : PeriodOneHminusOne) (z : ℂ) :
    2*z*((fderiv ℂ (fun p => hillHminusCanonicalPsi n (z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ),p)) q) h) =
      sourcePsiCandidateVariation ((n:ℕ):ℤ) (P.nativePsiRootMap n q:Coeff 2)
        (P.nativePsiRootDirection n q h:Coeff 2) z-
      sourcePsiCandidateVariation ((n:ℕ):ℤ) (P.nativePsiRootMap n q:Coeff 2)
        (P.nativePsiRootDirection n q h:Coeff 2) (-z) := by
  have hpsi : AnalyticAt ℂ (fun p => hillHminusCanonicalPsi n
      (z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ),p)) q :=
    (analyticOnNhd_hillHminusCanonicalPsi n (z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ),q)
      ⟨mem_univ _,mem_iUnion.mpr ⟨P.parent,P.subset hq⟩⟩).comp
      (f := fun p : PeriodOneHminusOne => (z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ),p))
      (analyticAt_const.prod analyticAt_id)
  have hN (w : ℂ) : AnalyticAt ℂ (fun p => sourcePsiCandidate ((n:ℕ):ℤ) (w,(P.nativePsiRootMap n p:Coeff 2))) q := by
    let hi := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 ((n:ℕ):ℤ)).ker.subtypeL
    have hco : AnalyticAt ℂ (fun p => (P.nativePsiRootMap n p:Coeff 2)) q := by
      simpa only [hi,Function.comp_def,Submodule.subtypeL_apply] using
        (hi.analyticAt _).comp (P.analytic_nativePsiRootMap n q hq)
    exact (analyticOnNhd_sourcePsiCandidate (by norm_num) (by norm_num) ((n:ℕ):ℤ)
      (w,(P.nativePsiRootMap n q:Coeff 2)) (mem_univ _)).comp
      (f := fun p : PeriodOneHminusOne => (w,(P.nativePsiRootMap n p:Coeff 2)))
      (analyticAt_const.prod hco)
  have he : (fun p => 2*z*hillHminusCanonicalPsi n (z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ),p)) =ᶠ[𝓝 q]
      (fun p => sourcePsiCandidate ((n:ℕ):ℤ) (z,(P.nativePsiRootMap n p:Coeff 2))-
        sourcePsiCandidate ((n:ℕ):ℤ) (-z,(P.nativePsiRootMap n p:Coeff 2))) := by
    filter_upwards [P.source_open.mem_nhds hq] with p hp
    exact P.canonicalPsi_frequency_identity n p hp z
  have hd := congrArg (fun L : PeriodOneHminusOne →L[ℂ] ℂ => L h) he.fderiv_eq
  rw [fderiv_const_mul hpsi.differentiableAt (2*z),fderiv_fun_sub (hN z).differentiableAt (hN (-z)).differentiableAt] at hd
  simp only [smul_apply,smul_eq_mul,sub_apply] at hd
  rw [P.fderiv_nativePsiCandidate_eq_root_variation n q hq h z,
    P.fderiv_nativePsiCandidate_eq_root_variation n q hq h (-z)] at hd
  exact hd

end NLS.KdV.HillProductEquationPatch
