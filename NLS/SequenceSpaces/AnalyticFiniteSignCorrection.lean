import NLS.SequenceSpaces.FiniteReweighting
import NLS.SequenceSpaces.WeightedSignChange
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! Eventually identical positive signs differ by an ACTUAL finite
weighted correction. Retain the SAME core and absorb that correction into
the stronger analytic remainder, on the SAME original neighborhood. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.WeightedCoeff

theorem exists_analytic_finite_sign_correction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : Set E) (e d : ℤ → Bool) (N : ℕ)
    (het : ∀ k : ℕ,N≤k → e ((k+1:ℕ):ℤ)=d ((k+1:ℕ):ℤ))
    (A : E → WeightedCoeff (Weight.sobolev 1) 2)
    (R : E → WeightedCoeff (Weight.sobolev 2) 2) (G : E → ℤ → ℂ)
    (CA CR : ℝ) (hCA : 0≤CA) (hCR : 0≤CR)
    (hAa : AnalyticOnNhd ℂ A U) (hRa : AnalyticOnNhd ℂ R U)
    (hAb : ∀ p∈U,‖A p‖≤CA) (hRb : ∀ p∈U,‖R p‖≤CR)
    (hAh : ∀ p∈U,∀ j : ℤ,j≤0 → (A p).val j=0)
    (hG : ∀ p∈U,∀ j : ℤ,G p j=if e j then -((A p).val j+(R p).val j) else (A p).val j+(R p).val j) :
    ∃ C : ℝ,∃ S : E → WeightedCoeff (Weight.sobolev 2) 2,
      0≤C ∧ AnalyticOnNhd ℂ S U ∧ ∀ p∈U,‖S p‖≤C ∧ ∀ j : ℤ,
        G p j=if d j then -((A p).val j+(S p).val j) else (A p).val j+(S p).val j := by
  classical
  let F := Finset.Icc (1:ℤ) (N:ℤ)
  let Q := finiteReweightingCLM (Weight.sobolev 1) (Weight.sobolev 2) F (p := 2)
  let T := (signChangeCLM (Weight.sobolev 2) d (p := 2)).comp (signChangeCLM (Weight.sobolev 2) e)
  have hTnorm (x : WeightedCoeff (Weight.sobolev 2) 2) : ‖T x‖=‖x‖ := by
    change ‖signChangeCLM _ d (signChangeCLM _ e x)‖=‖x‖
    rw [norm_signChangeCLM,norm_signChangeCLM]
  have hTc (x : WeightedCoeff (Weight.sobolev 2) 2) (j : ℤ) :
      (T x).val j=if d j then -(if e j then -x.val j else x.val j) else (if e j then -x.val j else x.val j) := by
    change (signChangeCLM _ d (signChangeCLM _ e x)).val j=_
    rw [signChangeCLM_apply,signChangeCLM_apply]
  let S := fun p => T (R p)+(T (Q (A p))-Q (A p))
  have hTRa : AnalyticOnNhd ℂ (fun p => T (R p)) U := fun p hp => (T.analyticAt _).comp (hRa p hp)
  have hQAa : AnalyticOnNhd ℂ (fun p => Q (A p)) U := fun p hp => (Q.analyticAt _).comp (hAa p hp)
  have hTQAa : AnalyticOnNhd ℂ (fun p => T (Q (A p))) U := fun p hp => (T.analyticAt _).comp (hQAa p hp)
  have hSa : AnalyticOnNhd ℂ S U := hTRa.add (hTQAa.sub hQAa)
  refine ⟨CR+2*‖Q‖*CA,S,by positivity,hSa,?_⟩
  intro p hp
  constructor
  · have hQb : ‖Q (A p)‖≤‖Q‖*CA :=
      (Q.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hAb p hp) (norm_nonneg _))
    calc
      ‖S p‖≤‖T (R p)‖+‖T (Q (A p))-Q (A p)‖ := norm_add_le _ _
      _≤CR+(‖T (Q (A p))‖+‖Q (A p)‖) := by
        rw [hTnorm]
        exact add_le_add (hRb p hp) (norm_sub_le _ _)
      _=CR+(‖Q (A p)‖+‖Q (A p)‖) := by rw [hTnorm]
      _≤CR+(‖Q‖*CA+‖Q‖*CA) := add_le_add le_rfl (add_le_add hQb hQb)
      _=CR+2*‖Q‖*CA := by ring
  intro j
  have hSc : (S p).val j=(T (R p)).val j+(T (Q (A p))).val j-(Q (A p)).val j := by
    simp only [S,add_val,sub_val];ring
  rw [hG p hp j,hSc,hTc,hTc,finiteReweightingCLM_apply]
  by_cases hjF : j∈F
  · rw [if_pos hjF]
    cases e j <;> cases d j <;> simp only [Bool.false_eq_true,↓reduceIte] <;> ring
  rw [if_neg hjF]
  by_cases hj : j≤0
  · rw [hAh p hp j hj]
    cases e j <;> cases d j <;> simp only [Bool.false_eq_true,↓reduceIte] <;> ring
  have hjpos : 0<j := by omega
  have hjN : (N:ℤ)<j := by
    simp only [F,Finset.mem_Icc] at hjF
    omega
  let k := j.toNat-1
  have hk : N≤k := by dsimp only [k];omega
  have hkj : ((k+1:ℕ):ℤ)=j := by dsimp only [k];omega
  have he := het k hk
  rw [hkj] at he
  rw [he]
  cases d j <;> simp only [Bool.false_eq_true,↓reduceIte] <;> ring

end NLS.WeightedCoeff
