import NLS.DifferentialPolynomial.JetOrderBounds


/-! # Integration by parts preserves any scalar grading increased by one under differentiation. -/

noncomputable section
set_option autoImplicit false
open MvPolynomial
namespace NLS.DifferentialPolynomial

def HasWeightedJetReduction (w : Jet → ℤ) (m : ℕ) (d D : ℤ) (p : Polynomial) : Prop :=
  ∃ q r : Polynomial, p = q+spatialDerivative r ∧ JetOrderLE q (m-1) ∧
    q.IsWeightedHomogeneous w d ∧ DerivativeOrderLE q D

namespace HasWeightedJetReduction
variable {w : Jet → ℤ} {m : ℕ} {d D : ℤ} {p p' : Polynomial}

theorem of_order (hp : JetOrderLE p (m-1))
    (hw : p.IsWeightedHomogeneous w d) (hD : DerivativeOrderLE p D) :
    HasWeightedJetReduction w m d D p := ⟨p,0,by simp,hp,hw,hD⟩

theorem zero : HasWeightedJetReduction w m d D 0 :=
  of_order (JetOrderLE.zero _) (isWeightedHomogeneous_zero _ _ _) (DerivativeOrderLE.zero _)

theorem add (hp : HasWeightedJetReduction w m d D p)
    (hp' : HasWeightedJetReduction w m d D p') : HasWeightedJetReduction w m d D (p+p') := by
  obtain ⟨q,r,he,hq,hw,hD⟩ := hp
  obtain ⟨q',r',he',hq',hw',hD'⟩ := hp'
  refine ⟨q+q',r+r',?_,hq.add hq',hw.add hw',hD.add hD'⟩
  rw [he,he',map_add]
  ring

theorem sum {ι : Type*} (S : Finset ι) (f : ι → Polynomial)
    (hf : ∀ i ∈ S, HasWeightedJetReduction w m d D (f i)) :
    HasWeightedJetReduction w m d D (∑ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (zero (w := w) (m := m) (d := d) (D := D))
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem add_spatialDerivative (hp : HasWeightedJetReduction w m d D p) (r : Polynomial) :
    HasWeightedJetReduction w m d D (p+spatialDerivative r) := by
  obtain ⟨q,s,he,hq,hw,hD⟩ := hp
  refine ⟨q,s+r,?_,hq,hw,hD⟩
  rw [he,map_add]
  ring
end HasWeightedJetReduction

private theorem lower_high_monomial_weighted (w : Jet → ℤ)
    (hstep : ∀ v, w (nextJet v) = w v+1)
    (t : Monomial) (z : ℂ) (v : Jet) (k : ℕ)
    (hv : v ∈ t.support) (hk : v.2 = k+1) (d D : ℤ)
    (hw : Finsupp.weight w t = d)
    (hD : Finsupp.weight derivativeWeight t ≤ D) (hbound : D ≤ 2*(k:ℤ)) :
    ∃ p r : Polynomial, MvPolynomial.monomial t z = p+spatialDerivative r ∧
      JetOrderLE p k ∧ p.IsWeightedHomogeneous w d ∧ DerivativeOrderLE p D := by
  let a : Jet := (v.1,k)
  let f : Polynomial := MvPolynomial.monomial (t-Finsupp.single v 1) z
  have ha : nextJet a = v := by ext <;> simp [a,nextJet,hk]
  have hwa : w v = w a+1 := by rw [← ha]; exact hstep a
  have hfD : DerivativeOrderLE f (D-((k:ℤ)+1)) :=
    Supported.monomial _ _ (by
      change Finsupp.weight derivativeWeight (t-Finsupp.single v 1) ≤ _
      rw [weight_erase_one _ t v hv]
      simp only [derivativeWeight,hk,Nat.cast_add,Nat.cast_one]
      omega)
  have hfw : f.IsWeightedHomogeneous w (d-w v) :=
    isWeightedHomogeneous_monomial _ _ _ (by rw [weight_erase_one _ t v hv,hw])
  have hj : JetOrderLE (spatialDerivative f) k :=
    JetOrderLE.of_derivativeOrder hfD.spatialDerivative (by omega)
  refine ⟨-(X a*spatialDerivative f),X a*f,?_,((JetOrderLE.X a).mul hj).neg,?_,?_⟩
  · rw [monomial_factor_jet t z v hv]
    change X v*f = -(X a*spatialDerivative f)+spatialDerivative (X a*f)
    rw [Derivation.leibniz,spatialDerivative_X,ha]
    simp only [smul_eq_mul]
    ring
  · convert! ((isWeightedHomogeneous_X (R := ℂ) w a).mul
      (homogeneous_spatialDerivative w 1 _ hstep hfw)).neg using 1
    rw [hwa]
    ring
  · convert ((DerivativeOrderLE.X a).mul hfD.spatialDerivative).neg using 1
    dsimp only [a]
    ring

theorem hasWeightedJetReduction_of_jetOrder (w : Jet → ℤ)
    (hstep : ∀ v, w (nextJet v) = w v+1) (m : ℕ) (hm : 1 ≤ m) (d D : ℤ)
    (hD : D ≤ 2*(m:ℤ)-2) (k : ℕ) (p : Polynomial)
    (hp : JetOrderLE p k) (hw : p.IsWeightedHomogeneous w d) (hd : DerivativeOrderLE p D) :
    HasWeightedJetReduction w m d D p := by
  classical
  induction k generalizing p with
  | zero => exact HasWeightedJetReduction.of_order (hp.mono (by omega)) hw hd
  | succ k ih =>
    by_cases hsmall : k+1 ≤ m-1
    · exact HasWeightedJetReduction.of_order (hp.mono hsmall) hw hd
    have hmk : m ≤ k+1 := by omega
    have ht (t : Monomial) (ht : t ∈ p.support) :
        HasWeightedJetReduction w m d D (MvPolynomial.monomial t (p.coeff t)) := by
      have hwt := hw (MvPolynomial.mem_support_iff.mp ht)
      by_cases hlow : ∀ v ∈ t.support, v.2 ≤ k
      · exact ih _ (Supported.monomial _ _ hlow)
          (isWeightedHomogeneous_monomial _ _ _ hwt) (Supported.monomial _ _ (hd t ht))
      · push Not at hlow
        obtain ⟨v,hv,hvk⟩ := hlow
        have he : v.2 = k+1 := by have := hp t ht v hv; omega
        obtain ⟨q,r,heq,hq,hqw,hqd⟩ := lower_high_monomial_weighted w hstep t (p.coeff t)
          v k hv he d D hwt (hd t ht) (by omega)
        rw [heq]
        exact (ih q hq hqw hqd).add_spatialDerivative r
    have hs := HasWeightedJetReduction.sum p.support
      (fun t => MvPolynomial.monomial t (p.coeff t)) ht
    simpa only [← p.as_sum] using hs

theorem exists_weighted_jet_reduction (w : Jet → ℤ)
    (hstep : ∀ v, w (nextJet v) = w v+1) (m : ℕ) (hm : 1 ≤ m)
    (p : Polynomial) (d : ℤ) (hw : p.IsWeightedHomogeneous w d)
    (hd : DerivativeOrderLE p (2*(m:ℤ)-2)) :
    HasWeightedJetReduction w m d (2*(m:ℤ)-2) p := by
  obtain ⟨k,hk⟩ := exists_jetOrderLE p
  exact hasWeightedJetReduction_of_jetOrder w hstep m hm d _ le_rfl k p hk hw hd

end NLS.DifferentialPolynomial
