import NLS.KdV.MiuraHillPsiNumerators
import NLS.KdV.HminusOneDirichletSheet

/-! Actual local Hill energy numerator families above every original real
H-minus-one source. One common source neighborhood supports ALL indices,
the exact physical shift and the preceding Dirichlet divisor data.
Agreement between different Miura charts is not yet asserted. -/
noncomputable section
open Set Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV
namespace HillHminusDirichletBall

def psiSource (B : HillHminusDirichletBall) (A : MiuraHillPsiFamily) : Set PeriodOneHminusOne :=
  B.source ∩ B.miuraBall.actionBall.lift ⁻¹' A.source

theorem psiSource_open (B : HillHminusDirichletBall) (A : MiuraHillPsiFamily) : IsOpen (B.psiSource A) := by
  have hl : ContinuousOn B.miuraBall.actionBall.lift B.source := B.miuraBall.actionBall.lift_analytic.continuousOn
  exact hl.isOpen_inter_preimage B.source_open A.source_open

theorem psiSource_subset_dirichletDomain (B : HillHminusDirichletBall) (A : MiuraHillPsiFamily) :
    B.psiSource A ⊆ hillHminusCanonicalDirichletDomain := by
  intro q hq
  exact mem_iUnion.mpr ⟨B,hq.1⟩

theorem real_mem_psiSource (B : HillHminusDirichletBall) (A : MiuraHillPsiFamily)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) (hreal : IsRealPeriodOneHminusOne q) :
    q ∈ B.psiSource A :=
  ⟨hq,A.real_mem_source ⟨B.miuraBall.actionBall.lift q,B.miuraBall.actionBall.lift_real q hq hreal⟩⟩

/-- The physical energy is shifted by the exact constant in the verified Miura image. -/
def psiNumerator (B : HillHminusDirichletBall) (A : MiuraHillPsiFamily) (n : ℕ+)
    (t : ℂ × PeriodOneHminusOne) : ℂ :=
  A.numerator n (t.1+(B.miuraBall.actionBall.shift:ℂ),B.miuraBall.actionBall.lift t.2)

theorem analytic_psiNumerator (B : HillHminusDirichletBall) (A : MiuraHillPsiFamily) (n : ℕ+) :
    AnalyticOnNhd ℂ (B.psiNumerator A n) (univ ×ˢ B.psiSource A) := by
  intro t ht
  have hl : AnalyticAt ℂ (fun x : ℂ × PeriodOneHminusOne => B.miuraBall.actionBall.lift x.2) t :=
    (B.miuraBall.actionBall.lift_analytic t.2 ht.2.1).comp (f := Prod.snd) analyticAt_snd
  exact (A.analytic_numerator n
    (t.1+(B.miuraBall.actionBall.shift:ℂ),B.miuraBall.actionBall.lift t.2) ⟨mem_univ _,ht.2.2⟩).comp
      (f := fun x : ℂ × PeriodOneHminusOne =>
        (x.1+(B.miuraBall.actionBall.shift:ℂ),B.miuraBall.actionBall.lift x.2))
      ((analyticAt_fst.add analyticAt_const).prod hl)

/-- Exact normalized positive periods after the ORIGINAL physical energy translation. -/
theorem psiNumerator_pullback_period (B : HillHminusDirichletBall) (A : MiuraHillPsiFamily)
    (n m : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ B.psiSource A)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
      (hillMiuraDiagonal (B.miuraBall.actionBall.lift q)) ((m:ℕ):ℤ)) :
    (2*Real.pi:ℂ)⁻¹*(∮ z in C((D.center:ℂ),D.radius),
      (2*z*B.psiNumerator A n (z^2-(B.miuraBall.actionBall.shift:ℂ),q))/
        sourceCanonicalRoot (by norm_num) (by norm_num)
          (hillMiuraDiagonal (B.miuraBall.actionBall.lift q)) z) = if m = n then 1 else 0 := by
  have he (z : ℂ) : B.psiNumerator A n (z^2-(B.miuraBall.actionBall.shift:ℂ),q) =
      A.numerator n (z^2,B.miuraBall.actionBall.lift q) := by
    simp only [psiNumerator,sub_add_cancel]
  simp_rw [he]
  exact A.numerator_pullback_period n m _ hq.2 D

/-- Every local original source has an actual positive-index period circle. -/
theorem nonempty_psiPeriodCircle (B : HillHminusDirichletBall) (A : MiuraHillPsiFamily)
    (q : PeriodOneHminusOne) (hq : q ∈ B.psiSource A) (m : ℕ+) :
    Nonempty (SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
      (hillMiuraDiagonal (B.miuraBall.actionBall.lift q)) ((m:ℕ):ℤ)) :=
  A.nonempty_periodCircle _ hq.2 m

end HillHminusDirichletBall

/-- Every real native H-minus-one source has an actual common all-index psi chart. -/
theorem exists_local_hminusHillPsiFamily (A : MiuraHillPsiFamily) (q : PeriodOneHminusOne)
    (hreal : IsRealPeriodOneHminusOne q) :
    ∃ B : HillHminusDirichletBall, q ∈ B.psiSource A := by
  obtain ⟨B,hB⟩ := exists_hillHminusDirichletBall q hreal
  exact ⟨B,B.real_mem_psiSource A q hB hreal⟩

end NLS.KdV
