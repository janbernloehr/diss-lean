import NLS.KdV.HillHminusOneRealMiuraSourcePsi
import NLS.ComplexAnalysis.ParametricOddSquareDescent

/-! # Entire energy candidates from actual rough Miura psi data

The actual normalized NLS numerator is antisymmetrized and divided by
twice the frequency with its analytic value at zero filled in. The exact
fixed Miura energy translation is retained. These are entire energy
candidates; their Hill root, energy-contour normalization and agreement
with the normalized Hill family require further identification proofs.
-/
noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.KdV
open NLS.ZakharovShabat NLS.ComplexAnalysis

def hillHminusMiuraSourcePsi (C : HillHminusMiuraChart)
    (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n) (n : ℤ)
    (x : ℂ × PeriodOneHminusOne) : ℂ :=
  sourcePsiCandidate n (x.1,(s n (C.criticalSource x.2) : Coeff 2))

def hillHminusMiuraEnergyPsi (C : HillHminusMiuraChart)
    (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n) (n : ℤ)
    (x : ℂ × PeriodOneHminusOne) : ℂ :=
  oddSquareDescent (fun z => hillHminusMiuraSourcePsi C s n (z,x.2) -
    hillHminusMiuraSourcePsi C s n (-z,x.2)) (x.1+C.energyShift)

theorem hillHminusMiuraEnergyPsi_factor (C : HillHminusMiuraChart)
    (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n) (n : ℤ)
    (q : PeriodOneHminusOne) (z : ℂ) :
    (2*z)*hillHminusMiuraEnergyPsi C s n (z^2-C.energyShift,q) =
      hillHminusMiuraSourcePsi C s n (z,q) - hillHminusMiuraSourcePsi C s n (-z,q) := by
  unfold hillHminusMiuraEnergyPsi
  rw [sub_add_cancel]
  apply oddSquareDescent_factor
  intro w
  simp only [neg_neg]
  ring

theorem analyticOnNhd_hillHminusMiuraEnergyPsi (C : HillHminusMiuraChart)
    (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n) {V : Set PeriodOneHminusOne}
    (hV : IsOpen V) (hs : ∀ n : ℤ, AnalyticOnNhd ℂ (fun q => s n (C.criticalSource q)) V)
    (n : ℤ) : AnalyticOnNhd ℂ (hillHminusMiuraEnergyPsi C s n) (univ ×ˢ V) := by
  have hphi : AnalyticOnNhd ℂ (hillHminusMiuraSourcePsi C s n) (univ ×ˢ V) := by
    intro x hx
    let i : DeletedCoeff 2 n →L[ℂ] Coeff 2 :=
      (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).ker.subtypeL
    have ha := (i.analyticAt (s n (C.criticalSource x.2))).comp
      (f := fun x : ℂ × PeriodOneHminusOne => s n (C.criticalSource x.2)) ((hs n x.2 hx.2).comp
      (f := fun x : ℂ × PeriodOneHminusOne => x.2) analyticAt_snd)
    exact (analyticOnNhd_sourcePsiCandidate (by simp) (by norm_num) n
      (x.1,(s n (C.criticalSource x.2) : Coeff 2)) (mem_univ _)).comp
        (f := fun x : ℂ × PeriodOneHminusOne => (x.1,(s n (C.criticalSource x.2) : Coeff 2)))
        (analyticAt_fst.prod ha)
  let F : ℂ × PeriodOneHminusOne → ℂ := fun x =>
    hillHminusMiuraSourcePsi C s n (x.1,x.2) - hillHminusMiuraSourcePsi C s n (-x.1,x.2)
  have hF : AnalyticOnNhd ℂ F (univ ×ˢ V) := by
    intro x hx
    exact (hphi x hx).sub ((hphi (-x.1,x.2) ⟨mem_univ _,hx.2⟩).comp
      (f := fun x : ℂ × PeriodOneHminusOne => (-x.1,x.2))
      ((analyticAt_fst.neg).prod analyticAt_snd))
  have hodd : ∀ q ∈ V, ∀ z, F (-z,q) = -F (z,q) := by
    intro q _ z
    dsimp [F]
    simp only [neg_neg]
    ring
  have hd := analyticOnNhd_parametric_oddSquareDescent F hV hF hodd
  intro x hx
  exact (hd (x.1+C.energyShift,x.2) ⟨mem_univ _,hx.2⟩).comp
    (f := fun x : ℂ × PeriodOneHminusOne => (x.1+C.energyShift,x.2))
    ((analyticAt_fst.add analyticAt_const).prod analyticAt_snd)

/-- Actual normalized NLS data exist near every physically real rough
potential, and their antisymmetrized energy candidates are jointly analytic
on one common neighborhood before every index. The periods retained here
are the original frequency periods, not yet energy periods. -/
theorem exists_hillHminus_real_entire_energyPsi (q0 : PeriodOneHminusOne)
    (hq0 : periodOneHminusConjugation q0 = q0) :
    ∃ C : HillHminusMiuraChart, ∃ V : Set PeriodOneHminusOne, ∃ W : Set (CoeffPair 2),
      ∃ s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n,
        IsOpen V ∧ q0 ∈ V ∧ V ⊆ C.domain ∧
        (∀ q ∈ C.domain, periodOneHminusConjugation q = q → q ∈ V) ∧
        0 < C.energyShift.re ∧ C.energyShift.im = 0 ∧
        SourcePsiNormalizedComplexExtension (by simp) (by norm_num) W s ∧
        (∀ q ∈ V, C.criticalSource q ∈ W) ∧
        (∀ n : ℤ, AnalyticOnNhd ℂ (hillHminusMiuraEnergyPsi C s n) (univ ×ˢ V)) ∧
        ∀ q ∈ V, ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
          sourcePsiRealCenteredContourFamily (by simp) (by norm_num) (C.criticalSource q) c R ∧
          ∀ n m : ℤ, (∮ z in C(c m,R m),
            sourcePsiContourIntegrandJoint (by simp) (by norm_num) n
              (z,((s n (C.criticalSource q) : Coeff 2),C.criticalSource q))) =
                (2*Real.pi : ℂ)*(if m = n then 1 else 0) := by
  obtain ⟨C,V,A,W,s,_,hshift,hshiftim,_,hV,hqV,hVC,hrealV,_,_,_,_,_,S,hVW,hs,hperiods⟩ :=
    exists_hillHminus_real_sourcePsi_data q0 hq0
  exact ⟨C,V,W,s,hV,hqV,hVC,hrealV,hshift,hshiftim,S,hVW,
    analyticOnNhd_hillHminusMiuraEnergyPsi C s hV hs,hperiods⟩

end NLS.KdV
