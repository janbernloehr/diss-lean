import NLS.KdV.MiuraWeightedSecondMoments
import NLS.KdV.HillHminusFixedPhysicalNumerators

/-! # Constructed weighted moment germs at every real rough Hill source

These are actual analytic moment sums on one common local rough-source
domain, retaining the physical numerator branch. The Hill frequency
identity, Miura-chart independence and action descent remain separate.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.KdV

theorem exists_hillHminus_weighted_secondMoment_chart
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (M : ℝ) :
    ∃ P : HillHminusPsiChart, ∃ c : ℝ, ∃ W : Set (CoeffPair 2),
      ∃ A : SourceAbelianMomentAtlas (by norm_num) (by norm_num) W P.family.roots,
      ∃ T : Set PeriodOneHminusOne, 0<c ∧ M<c ∧ P.miura.energyShift=(c : ℂ)^2 ∧
        IsOpen T ∧ q ∈ T ∧ T ⊆ P.source ∧
        (∀ a∈P.miura.domain, IsRealPeriodOneHminusOne a → ∀ k : ℤ,
          P.miura.lift a (-k)=conj (P.miura.lift a k)) ∧
        (∀ a∈P.miura.domain, hillHminusRadicand a (-P.miura.energyShift)≠0) ∧
        (∀ n : ℤ, AnalyticOnNhd ℂ
          (fun a => A.weightedSecondMomentSum n (hillMiuraDiagonal (P.miura.lift a))) T) ∧
        (∀ a ∈ T, ∀ n : ℤ, Summable
          (fun k : ℤ => ‖(k : ℂ)*A.moment n k 2 (hillMiuraDiagonal (P.miura.lift a))‖)) ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ T, ∀ n : ℤ,
          ‖A.weightedSecondMomentSum n (hillMiuraDiagonal (P.miura.lift a))‖ ≤ (1+‖(n : ℂ)‖)*C := by
  obtain ⟨P,c,hc,hMc,hshift,hqP,hreal,houtside,H⟩ :=
    exists_hillHminusPsiChart_real_form_outside_shift q hq M
  obtain ⟨W,A,U,hU,_hUc,hrealU,hsub,hsum,ha,hbound⟩ :=
    P.family.exists_weighted_secondMoment_atlas H
  let F : PeriodOneHminusOne → CoeffPair 2 := fun a => hillMiuraDiagonal (P.miura.lift a)
  have hF : AnalyticOnNhd ℂ F P.miura.domain := by
    intro a ha
    exact (hillMiuraDiagonal.analyticAt _).comp (P.miura.lift_analytic a ha)
  have hqU : F q ∈ U :=
    hrealU (isRealType_hillMiuraDiagonal ⟨P.miura.lift q,hreal q hqP.1 hq⟩)
  obtain ⟨S,hS,hqS,hSU,C,hC,hCb⟩ := hbound (F q) hqU
  let T := P.miura.domain ∩ F ⁻¹' S
  have hT : IsOpen T := hF.continuousOn.isOpen_inter_preimage P.miura.domain_open hS
  have hTU (a : PeriodOneHminusOne) (ha : a ∈ T) : F a ∈ U := hSU ha.2
  have hTP : T ⊆ P.source := fun a ha => ⟨ha.1,(hsub (hTU a ha)).2⟩
  refine ⟨P,c,W,A,T,hc,hMc,hshift,hT,⟨hqP.1,hqS⟩,hTP,hreal,houtside,?_,?_,C,hC,?_⟩
  · intro n a haT
    exact (ha n (F a) (hTU a haT)).comp (hF a haT.1)
  · intro a haT n
    exact hsum (F a) (hTU a haT) n
  · intro a haT n
    exact hCb (F a) haT.2 n

end NLS.KdV
