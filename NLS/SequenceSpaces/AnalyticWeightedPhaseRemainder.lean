import NLS.SequenceSpaces.Weighted
import NLS.SequenceSpaces.HolderEmbedding
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! A bounded analytic inverse phase and its weighted error split an ACTUAL
weighted packet into an analytic principal packet and a one-derivative remainder. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.Coeff

theorem weighted_phase_compensation_of_positive
    (P : Coeff 2) (N M : Coeff ⊤) (phase : ℕ+ → ℂ)
    (hP : ∀ j : ℤ, j≤0 → P j=0)
    (hM : ∀ n : ℕ+, M (n:ℤ)=(1+(n:ℂ))*(phase n-1))
    (hN : ∀ n : ℕ+, phase n*N (n:ℤ)=1) :
    ∀ j : ℤ, M j*N j*P j=(Weight.sobolev 1 j:ℂ)*(P j-N j*P j) := by
  have hpos (n : ℕ+) : M (n:ℤ)*N (n:ℤ)*P (n:ℤ)=
      (Weight.sobolev 1 (n:ℤ):ℂ)*(P (n:ℤ)-N (n:ℤ)*P (n:ℤ)) := by
    have hw : (Weight.sobolev 1 (n:ℤ):ℂ)=1+(n:ℂ) := by
      simp only [Weight.sobolev_apply,Real.rpow_one,Int.cast_natCast,
        abs_of_pos (by positivity : (0:ℝ)<n),Complex.ofReal_add,Complex.ofReal_one,Complex.ofReal_natCast]
    rw [hM n,hw]
    linear_combination (norm := ring) ((1+(n:ℂ))*P (n:ℤ))*(hN n)
  intro j
  by_cases hj : 0<j
  · let n : ℕ+ := ⟨j.toNat,by omega⟩
    have hn : (n:ℤ)=j := Int.toNat_of_nonneg hj.le
    exact hn ▸ hpos n
  · simp only [hP j (by omega),mul_zero,sub_self]

theorem exists_common_analytic_phase_packet_data
    {E Q : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup Q] [NormedSpace ℂ Q]
    (L : E →L[ℂ] Q) (V W : Set E) (Z : Set Q) (q : E)
    (hV : IsOpen V) (hW : IsOpen W) (hZ : IsOpen Z) (hqV : q∈V) (hqW : q∈W) (hqZ : L q∈Z)
    (P : Q → Coeff 2) (F : E → Coeff 2) (N : Q → Coeff ⊤) (M : E → Coeff ⊤)
    (phase invPhase : ℕ+ → Q → ℂ) (Valid : Q → Prop)
    (CF CN CM : ℝ)
    (hFa : AnalyticOnNhd ℂ F V) (hNa : AnalyticOnNhd ℂ N Z) (hMa : AnalyticOnNhd ℂ M W)
    (hFb : ∀ p∈V, ‖F p‖≤CF) (hNb : ∀ a∈Z, ‖N a‖≤CN) (hMb : ∀ p∈W, ‖M p‖≤CM)
    (hFc : ∀ p∈V, ∀ j : ℤ, F p j=(Weight.sobolev 1 j:ℂ)*P (L p) j)
    (hP : ∀ p∈V, ∀ j : ℤ, j≤0 → P (L p) j=0)
    (hM : ∀ p∈W, ∀ n : ℕ+, M p (n:ℤ)=(1+(n:ℂ))*(phase n (L p)-1))
    (hN : ∀ a∈Z, ∀ n : ℕ+, phase n a*N a (n:ℤ)=1)
    (hInv : ∀ a∈Z, ∀ n : ℕ+, N a (n:ℤ)=invPhase n a)
    (hValid : ∀ p∈V, Valid (L p)) :
    ∃ U : Set E, IsOpen U ∧ q∈U ∧ AnalyticOnNhd ℂ F U ∧
      AnalyticOnNhd ℂ (fun p => N (L p)) U ∧ AnalyticOnNhd ℂ M U ∧
      ∀ p∈U, Valid (L p) ∧ ‖F p‖≤CF ∧ ‖N (L p)‖≤CN ∧ ‖M p‖≤CM ∧
        (∀ j : ℤ, F p j=(Weight.sobolev 1 j:ℂ)*P (L p) j) ∧
        (∀ j : ℤ, M p j*N (L p) j*P (L p) j=
          (Weight.sobolev 1 j:ℂ)*(P (L p) j-N (L p) j*P (L p) j)) ∧
        ∀ n : ℕ+, N (L p) (n:ℤ)=invPhase n (L p) := by
  let U := (V∩W)∩L ⁻¹' Z
  refine ⟨U,(hV.inter hW).inter (hZ.preimage L.continuous),⟨⟨hqV,hqW⟩,hqZ⟩,
    (fun p hp => hFa p hp.1.1),(fun p hp => (hNa (L p) hp.2).comp (L.analyticAt p)),
    (fun p hp => hMa p hp.1.2),?_⟩
  intro p hp
  exact ⟨hValid p hp.1.1,hFb p hp.1.1,hNb (L p) hp.2,hMb p hp.1.2,hFc p hp.1.1,
    weighted_phase_compensation_of_positive (P (L p)) (N (L p)) (M p)
      (fun n => phase n (L p)) (hP p hp.1.1) (hM p hp.1.2) (hN (L p) hp.2),hInv (L p) hp.2⟩

theorem exists_analytic_weighted_phase_remainder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : Set E) (P F : E → Coeff 2) (N M : E → Coeff ⊤)
    (CF CN CM : ℝ) (hCN : 0≤CN) (hCM : 0≤CM)
    (hFa : AnalyticOnNhd ℂ F U) (hNa : AnalyticOnNhd ℂ N U) (hMa : AnalyticOnNhd ℂ M U)
    (hFb : ∀ p∈U, ‖F p‖≤CF) (hNb : ∀ p∈U, ‖N p‖≤CN) (hMb : ∀ p∈U, ‖M p‖≤CM)
    (hFc : ∀ p∈U, ∀ j : ℤ, F p j=(Weight.sobolev 1 j:ℂ)*P p j)
    (hc : ∀ p∈U, ∀ j : ℤ, M p j*N p j*P p j=
      (Weight.sobolev 1 j:ℂ)*(P p j-N p j*P p j)) :
    ∃ A : E → WeightedCoeff (Weight.sobolev 1) 2, ∃ R : E → WeightedCoeff (Weight.sobolev 2) 2,
      AnalyticOnNhd ℂ A U ∧ AnalyticOnNhd ℂ R U ∧ ∀ p∈U,
        ‖A p‖≤CN*CF ∧ ‖R p‖≤CM*(CN*CF) ∧
        (∀ j : ℤ, (A p).val j=N p j*P p j) ∧
        ∀ j : ℤ, (R p).val j=P p j-(A p).val j := by
  let F0 := fun p => holderProduct (q := 2) (N p) (F p)
  let J1 := (WeightedCoeff.weightIsometry (Weight.sobolev 1) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap
  let J2 := (WeightedCoeff.weightIsometry (Weight.sobolev 2) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap
  let A := fun p => J1 (F0 p)
  let R := fun p => J2 (holderProduct (q := 2) (M p) (F0 p))
  have hF0a : AnalyticOnNhd ℂ F0 U := fun p hp =>
    ((holderProduct (p := ⊤) (r := 2) (q := 2)).analyticAt_bilinear _).comp₂ (hNa p hp) (hFa p hp)
  have hAa : AnalyticOnNhd ℂ A U := fun p hp => (J1.analyticAt _).comp (hF0a p hp)
  have hRa : AnalyticOnNhd ℂ R U := fun p hp =>
    (J2.analyticAt _).comp (((holderProduct (p := ⊤) (r := 2) (q := 2)).analyticAt_bilinear _).comp₂
      (hMa p hp) (hF0a p hp))
  have hF0b (p) (hp : p∈U) : ‖F0 p‖≤CN*CF :=
    (norm_holderProduct_le _ _).trans (mul_le_mul (hNb p hp) (hFb p hp) (norm_nonneg _) hCN)
  have hAc (p) (hp : p∈U) (j : ℤ) : (A p).val j=N p j*P p j := by
    change (N p j*F p j)/(Weight.sobolev 1 j:ℂ)=_
    rw [hFc p hp j,mul_left_comm,mul_div_cancel_left₀ _ (Weight.complex_ne_zero _ _)]
  refine ⟨A,R,hAa,hRa,?_⟩
  intro p hp
  refine ⟨?_,?_,hAc p hp,?_⟩
  · exact ((WeightedCoeff.weightIsometry (Weight.sobolev 1) 2).symm.norm_map (F0 p)).le.trans (hF0b p hp)
  · exact ((WeightedCoeff.weightIsometry (Weight.sobolev 2) 2).symm.norm_map _).le.trans
      ((norm_holderProduct_le _ _).trans (mul_le_mul (hMb p hp) (hF0b p hp) (norm_nonneg _) hCM))
  · intro j
    have hw : (Weight.sobolev 2 j:ℂ)=(Weight.sobolev 1 j:ℂ)*(Weight.sobolev 1 j:ℂ) := by
      rw [show (2:ℝ)=1+1 by norm_num,Weight.sobolev_add,Complex.ofReal_mul]
    change (M p j*(N p j*F p j))/(Weight.sobolev 2 j:ℂ)=_
    rw [hFc p hp j,hAc p hp j,hw]
    apply (div_eq_iff (mul_ne_zero (Weight.complex_ne_zero _ _) (Weight.complex_ne_zero _ _))).mpr
    linear_combination (norm := ring) (Weight.sobolev 1 j:ℂ)*(hc p hp j)

end NLS.Coeff
