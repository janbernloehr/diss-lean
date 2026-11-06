import NLS.KdV.MiuraDirichletSignedSymmetry
import NLS.KdV.HillHminusPrescribedSheets

noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.KdV

/-- The actual ordinary-source anti-discriminant has the SAME value
at opposite nonzero Miura frequencies. This fixes the prescribed sheet
used at the negative Dirichlet terminal as well. -/
theorem sourceAntiDiscriminant_sourcePhase_miura_neg (u : Coeff 2)
    (z : ℂ) (hz : z≠0) :
    sourceAntiDiscriminantCandidate (by simp) (by norm_num)
      (sourcePhase (hillMiuraDiagonal u)) (-z)=
      sourceAntiDiscriminantCandidate (by simp) (by norm_num)
        (sourcePhase (hillMiuraDiagonal u)) z := by
  rw [sourceAntiDiscriminant_sourcePhase_miura u (-z) (neg_ne_zero.mpr hz),
    neg_sq,sourceAntiDiscriminant_sourcePhase_miura u z hz]

namespace HillHminusPsiChart

theorem dirichletFrequency_neg_of_real (P : HillHminusPsiChart)
    (a : PeriodOneHminusOne)
    (hreal : ∀ k : ℤ, P.miura.lift a (-k)=conj (P.miura.lift a k)) (n : ℤ) :
    P.dirichletFrequency (-n) a= -P.dirichletFrequency n a :=
  hillMiuraDiracDirichlet_neg ⟨P.miura.lift a,hreal⟩ n

theorem dirichletFrequency_zero_of_real (P : HillHminusPsiChart)
    (a : PeriodOneHminusOne)
    (hreal : ∀ k : ℤ, P.miura.lift a (-k)=conj (P.miura.lift a k)) :
    P.dirichletFrequency 0 a=0 := hillMiuraDiracDirichlet_zero ⟨P.miura.lift a,hreal⟩

/-- The positive and negative canonical endpoint slots reverse exactly
under negation at the actual ordinary source. This includes complex
sources and every low or collapsed slot. -/
theorem sourcePhase_periodic_endpoint_reflection (P : HillHminusPsiChart)
    (a : PeriodOneHminusOne) : SourcePeriodicReflection (by simp) (by norm_num)
      (P.dirichletSource a) :=
  (sourcePeriodicReflection_hillMiuraDiagonal (P.miura.lift a)).sourcePhase

/-- The actual ORIGINAL physical sheet is also the prescribed sheet
at the canonically labelled NEGATIVE frequency. Its sign is unchanged. -/
theorem dirichletSheet_eq_negative_sourcePhase (P : HillHminusPsiChart)
    (n : ℕ+) (a : PeriodOneHminusOne) (ha : a∈P.source)
    (hreal : ∀ k : ℤ, P.miura.lift a (-k)=conj (P.miura.lift a k))
    (hz : P.dirichletFrequency (n:ℕ) a≠0) :
    P.dirichletSheet n a=
      sourceBoundaryTerminalAntiDiscriminant (by simp) (by norm_num) .dirichlet
        (-((n:ℕ):ℤ)) (P.dirichletSource a) := by
  unfold sourceBoundaryTerminalAntiDiscriminant
  rw [← P.dirichletFrequency_eq_sourcePhase,P.dirichletFrequency_neg_of_real a hreal]
  change P.dirichletSheet n a=sourceAntiDiscriminantCandidate (by simp) (by norm_num)
    (sourcePhase (hillMiuraDiagonal (P.miura.lift a))) (-P.dirichletFrequency (n:ℕ) a)
  rw [sourceAntiDiscriminant_sourcePhase_miura_neg _ _ hz]
  have hpos := P.dirichletSheet_eq_sourcePhase n a ha hz
  unfold sourceBoundaryTerminalAntiDiscriminant at hpos
  rw [← P.dirichletFrequency_eq_sourcePhase] at hpos
  exact hpos

/-- The SAME prescribed sheet passes through both actual signed
Dirichlet terminals, including every regular terminal of a low gap. -/
theorem prescribedRoot_negative_dirichlet_base (P : HillHminusPsiChart)
    (n : ℕ+) (a : PeriodOneHminusOne) (ha : a∈P.source)
    (hreal : ∀ k : ℤ, P.miura.lift a (-k)=conj (P.miura.lift a k))
    (hz : P.dirichletFrequency (n:ℕ) a≠0) (hw : P.dirichletSheet n a≠0) :
    let μ := canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet
      (P.dirichletSource a) (-((n:ℕ):ℤ))
    (μ,P.dirichletSource a)∈sourceAngularRootSheetDomain (by simp) (P.dirichletSheet n a) ∧
      sourceAngularRootSheet (by simp) (P.dirichletSheet n a) (μ,P.dirichletSource a)=
        P.dirichletSheet n a := by
  have hn : sourceAntiDiscriminantCandidate (by simp) (by norm_num) (P.dirichletSource a)
      (canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet
        (P.dirichletSource a) (-((n:ℕ):ℤ)))≠0 := by
    change sourceBoundaryTerminalAntiDiscriminant (by simp) (by norm_num) .dirichlet
      (-((n:ℕ):ℤ)) (P.dirichletSource a)≠0
    rw [← P.dirichletSheet_eq_negative_sourcePhase n a ha hreal hz]
    exact hw
  have hs := sourceAngularRootSheet_dirichlet_base (by simp) (by norm_num)
    (P.dirichletSource a) (-((n:ℕ):ℤ)) hn
  dsimp only at hs ⊢
  have he := P.dirichletSheet_eq_negative_sourcePhase n a ha hreal hz
  change P.dirichletSheet n a=sourceAntiDiscriminantCandidate (by simp) (by norm_num)
    (P.dirichletSource a) (canonicalPeriodOneBoundaryRoots (by simp) (by norm_num)
      .dirichlet (P.dirichletSource a) (-((n:ℕ):ℤ))) at he
  rw [← he] at hs
  exact hs

end HillHminusPsiChart
end NLS.KdV
