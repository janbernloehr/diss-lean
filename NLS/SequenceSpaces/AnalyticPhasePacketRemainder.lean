import NLS.SequenceSpaces.AnalyticWeightedPhaseRemainder
import NLS.SequenceSpaces.SobolevHomogeneous

/-! A further actual phase can be removed from the SAME analytic h1
packet, adding its h2 error to an already proved h2 remainder. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.Coeff

theorem exists_analytic_phase_packet_remainder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (V W : Set E) (hV : IsOpen V) (hW : IsOpen W) (q : E) (hqV : q∈V) (hqW : q∈W)
    (P : E → Coeff 2) (A0 : E → WeightedCoeff (Weight.sobolev 1) 2)
    (R0 : E → WeightedCoeff (Weight.sobolev 2) 2) (N M : E → Coeff ⊤) (phase : ℕ+ → E → ℂ)
    (CA CR CN CM : ℝ) (hCN : 0≤CN) (hCM : 0≤CM)
    (hA0a : AnalyticOnNhd ℂ A0 V) (hR0a : AnalyticOnNhd ℂ R0 V)
    (hNa : AnalyticOnNhd ℂ N W) (hMa : AnalyticOnNhd ℂ M W)
    (hA0b : ∀ p∈V,‖A0 p‖≤CA) (hR0b : ∀ p∈V,‖R0 p‖≤CR)
    (hNb : ∀ p∈W,‖N p‖≤CN) (hMb : ∀ p∈W,‖M p‖≤CM)
    (hRc : ∀ p∈V,∀ j : ℤ,(R0 p).val j=P p j-(A0 p).val j)
    (hAh : ∀ p∈V,∀ j : ℤ,j≤0 → (A0 p).val j=0)
    (hMc : ∀ p∈W,∀ n : ℕ+,M p (n:ℤ)=(1+(n:ℂ))*(phase n p-1))
    (hNc : ∀ p∈W,∀ n : ℕ+,phase n p*N p (n:ℤ)=1) :
    ∃ U : Set E,IsOpen U ∧ q∈U ∧ U⊆V ∧ U⊆W ∧
      ∃ A : E → WeightedCoeff (Weight.sobolev 1) 2,∃ R : E → WeightedCoeff (Weight.sobolev 2) 2,
        AnalyticOnNhd ℂ A U ∧ AnalyticOnNhd ℂ R U ∧ ∀ p∈U,
          ‖A p‖≤CN*CA ∧ ‖R p‖≤CR+CM*(CN*CA) ∧
          (∀ j : ℤ,(R p).val j=P p j-(A p).val j) ∧
          (∀ j : ℤ,j≤0 → (A p).val j=0) ∧ ∀ j : ℤ,(A p).val j=N p j*(A0 p).val j := by
  let U := V∩W
  let J := (WeightedCoeff.weightIsometry (Weight.sobolev 1) 2).toContinuousLinearEquiv.toContinuousLinearMap
  let F := fun p => J (A0 p)
  let P0 := fun p => WeightedCoeff.sobolevToL2 (by norm_num : (0:ℝ)≤1) (A0 p)
  have hFa : AnalyticOnNhd ℂ F U := fun p hp => (J.analyticAt _).comp (hA0a p hp.1)
  have hFb (p) (hp : p∈U) : ‖F p‖≤CA :=
    ((WeightedCoeff.weightIsometry (Weight.sobolev 1) 2).norm_map _).le.trans (hA0b p hp.1)
  have hFc (p) (_hp : p∈U) (j : ℤ) : F p j=(Weight.sobolev 1 j:ℂ)*P0 p j := by
    simp only [P0,WeightedCoeff.sobolevToL2_apply]
    rfl
  have hcomp (p) (hp : p∈U) : ∀ j : ℤ,M p j*N p j*P0 p j=
      (Weight.sobolev 1 j:ℂ)*(P0 p j-N p j*P0 p j) :=
    weighted_phase_compensation_of_positive (P0 p) (N p) (M p) (fun n => phase n p)
      (fun j hj => by simpa only [P0,WeightedCoeff.sobolevToL2_apply] using hAh p hp.1 j hj)
      (hMc p hp.2) (hNc p hp.2)
  obtain ⟨A,S,hAa,hSa,hd⟩ := exists_analytic_weighted_phase_remainder U P0 F N M CA CN CM hCN hCM hFa
    (hNa.mono inter_subset_right) (hMa.mono inter_subset_right) hFb
    (fun p hp => hNb p hp.2) (fun p hp => hMb p hp.2) hFc hcomp
  refine ⟨U,hV.inter hW,⟨hqV,hqW⟩,inter_subset_left,inter_subset_right,A,(fun p => R0 p+S p),
    hAa,(hR0a.mono inter_subset_left).add hSa,?_⟩
  intro p hp
  have hAc (j : ℤ) : (A p).val j=N p j*(A0 p).val j := by
    simpa only [P0,WeightedCoeff.sobolevToL2_apply] using (hd p hp).2.2.1 j
  refine ⟨(hd p hp).1,(norm_add_le _ _).trans (add_le_add (hR0b p hp.1) (hd p hp).2.1),?_,?_,hAc⟩
  · intro j
    rw [WeightedCoeff.add_val,hRc p hp.1 j,(hd p hp).2.2.2 j]
    simp only [P0,WeightedCoeff.sobolevToL2_apply]
    ring
  · intro j hj
    rw [hAc j,hAh p hp.1 j hj,mul_zero]

end NLS.Coeff
