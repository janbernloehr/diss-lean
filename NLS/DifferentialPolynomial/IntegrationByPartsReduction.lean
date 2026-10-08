import NLS.DifferentialPolynomial.JetOrderBounds

/-! # Polynomial integration by parts with preservation of gradings

A polynomial with at most 2m-2 derivatives in each monomial is equivalent,
modulo a total spatial derivative, to one involving only jets through m-1.
The reduction preserves homogeneous total weight, field balance, and the
bound on the total number of derivatives.
-/
noncomputable section
open MvPolynomial
namespace NLS.DifferentialPolynomial

/-- An explicit polynomial equality records the discarded total derivative. -/
def HasJetReduction (m : ℕ) (d c D : ℤ) (p : Polynomial) : Prop :=
  ∃ q r : Polynomial, p = q+spatialDerivative r ∧ JetOrderLE q (m-1) ∧
    q.IsWeightedHomogeneous totalWeight d ∧ q.IsWeightedHomogeneous fieldCharge c ∧
    DerivativeOrderLE q D

namespace HasJetReduction
variable {m : ℕ} {d c D : ℤ} {p p' : Polynomial}

theorem of_order (hp : JetOrderLE p (m-1))
    (hw : p.IsWeightedHomogeneous totalWeight d) (hc : p.IsWeightedHomogeneous fieldCharge c)
    (hD : DerivativeOrderLE p D) : HasJetReduction m d c D p :=
  ⟨p,0,by simp,hp,hw,hc,hD⟩

theorem zero : HasJetReduction m d c D 0 :=
  of_order (JetOrderLE.zero _) (isWeightedHomogeneous_zero _ _ _)
    (isWeightedHomogeneous_zero _ _ _) (DerivativeOrderLE.zero _)

theorem add (hp : HasJetReduction m d c D p) (hp' : HasJetReduction m d c D p') :
    HasJetReduction m d c D (p+p') := by
  obtain ⟨q,r,he,hq,hw,hc,hD⟩ := hp
  obtain ⟨q',r',he',hq',hw',hc',hD'⟩ := hp'
  refine ⟨q+q',r+r',?_,hq.add hq',hw.add hw',hc.add hc',hD.add hD'⟩
  rw [he,he',map_add]
  ring

theorem sum {ι : Type*} (S : Finset ι) (f : ι → Polynomial)
    (hf : ∀ i ∈ S, HasJetReduction m d c D (f i)) :
    HasJetReduction m d c D (∑ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (zero (m := m) (d := d) (c := c) (D := D))
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- Adding a total derivative changes only the explicitly recorded primitive. -/
theorem add_spatialDerivative (hp : HasJetReduction m d c D p) (r : Polynomial) :
    HasJetReduction m d c D (p+spatialDerivative r) := by
  obtain ⟨q,s,he,hq,hw,hc,hD⟩ := hp
  refine ⟨q,s+r,?_,hq,hw,hc,hD⟩
  rw [he,map_add]
  ring
end HasJetReduction

/-- One integration-by-parts step lowers the unique high derivative.
The other product is controlled by its total derivative count. -/
private theorem lower_high_monomial (t : Monomial) (z : ℂ) (v : Jet) (k : ℕ)
    (hv : v ∈ t.support) (hk : v.2 = k+1) (d c D : ℤ)
    (hw : Finsupp.weight totalWeight t = d) (hc : Finsupp.weight fieldCharge t = c)
    (hD : Finsupp.weight derivativeWeight t ≤ D) (hbound : D ≤ 2*(k:ℤ)) :
    ∃ p r : Polynomial, MvPolynomial.monomial t z = p+spatialDerivative r ∧
      JetOrderLE p k ∧ p.IsWeightedHomogeneous totalWeight d ∧
      p.IsWeightedHomogeneous fieldCharge c ∧ DerivativeOrderLE p D := by
  let a : Jet := (v.1,k)
  let f : Polynomial := MvPolynomial.monomial (t-Finsupp.single v 1) z
  have ha : nextJet a = v := by ext <;> simp [a,nextJet,hk]
  have hfD : DerivativeOrderLE f (D-((k:ℤ)+1)) :=
    Supported.monomial _ _ (by
      change Finsupp.weight derivativeWeight (t-Finsupp.single v 1) ≤ _
      rw [weight_erase_one _ t v hv]
      simp only [derivativeWeight,hk,Nat.cast_add,Nat.cast_one]
      omega)
  have hfw : f.IsWeightedHomogeneous totalWeight (d-((k:ℤ)+2)) :=
    isWeightedHomogeneous_monomial _ _ _ (by
      rw [weight_erase_one _ t v hv,hw]
      simp [totalWeight,hk]
      ring)
  have hfc : f.IsWeightedHomogeneous fieldCharge (c-fieldCharge v) :=
    isWeightedHomogeneous_monomial _ _ _ (by rw [weight_erase_one _ t v hv,hc])
  have hj : JetOrderLE (spatialDerivative f) k :=
    JetOrderLE.of_derivativeOrder hfD.spatialDerivative (by omega)
  refine ⟨-(X a*spatialDerivative f),X a*f,?_,((JetOrderLE.X a).mul hj).neg,?_,?_,?_⟩
  · rw [monomial_factor_jet t z v hv]
    change X v*f = -(X a*spatialDerivative f)+spatialDerivative (X a*f)
    rw [Derivation.leibniz,spatialDerivative_X,ha]
    simp only [smul_eq_mul]
    ring
  · convert! ((isWeightedHomogeneous_X (R := ℂ) totalWeight a).mul
      (totalWeight_spatialDerivative hfw)).neg using 1
    dsimp only [totalWeight,a]
    ring
  · convert! ((isWeightedHomogeneous_X (R := ℂ) fieldCharge a).mul
      (fieldCharge_spatialDerivative hfc)).neg using 1
    dsimp only [fieldCharge,a]
    ring
  · convert ((DerivativeOrderLE.X a).mul hfD.spatialDerivative).neg using 1
    dsimp only [a]
    ring

/-- The total derivative bound makes the repeated polynomial reduction terminate.
All homogeneous gradings needed by Appendix H are preserved. -/
theorem hasJetReduction_of_jetOrder (m : ℕ) (hm : 1 ≤ m) (d c D : ℤ)
    (hD : D ≤ 2*(m:ℤ)-2) (k : ℕ) (p : Polynomial)
    (hp : JetOrderLE p k) (hw : p.IsWeightedHomogeneous totalWeight d)
    (hc : p.IsWeightedHomogeneous fieldCharge c) (hd : DerivativeOrderLE p D) :
    HasJetReduction m d c D p := by
  classical
  induction k generalizing p with
  | zero => exact HasJetReduction.of_order (hp.mono (by omega)) hw hc hd
  | succ k ih =>
    by_cases hsmall : k+1 ≤ m-1
    · exact HasJetReduction.of_order (hp.mono hsmall) hw hc hd
    have hmk : m ≤ k+1 := by omega
    have ht (t : Monomial) (ht : t ∈ p.support) :
        HasJetReduction m d c D (MvPolynomial.monomial t (p.coeff t)) := by
      have hwt := hw (MvPolynomial.mem_support_iff.mp ht)
      have hct := hc (MvPolynomial.mem_support_iff.mp ht)
      by_cases hlow : ∀ v ∈ t.support, v.2 ≤ k
      · exact ih _ (Supported.monomial _ _ hlow)
          (isWeightedHomogeneous_monomial _ _ _ hwt)
          (isWeightedHomogeneous_monomial _ _ _ hct)
          (Supported.monomial _ _ (hd t ht))
      · push Not at hlow
        obtain ⟨v,hv,hvk⟩ := hlow
        have he : v.2 = k+1 := by have := hp t ht v hv; omega
        obtain ⟨q,r,heq,hq,hqw,hqc,hqd⟩ := lower_high_monomial t (p.coeff t) v k hv he
          d c D hwt hct (hd t ht) (by omega)
        rw [heq]
        exact (ih q hq hqw hqc hqd).add_spatialDerivative r
    have hs := HasJetReduction.sum p.support (fun t => MvPolynomial.monomial t (p.coeff t)) ht
    simpa only [← p.as_sum] using hs

/-- Every polynomial with at most 2m-2 derivatives per monomial can be lowered
to jets through m-1 modulo an actual total derivative, with both gradings intact. -/
theorem exists_graded_jet_reduction (m : ℕ) (hm : 1 ≤ m) (p : Polynomial) (d c : ℤ)
    (hw : p.IsWeightedHomogeneous totalWeight d) (hc : p.IsWeightedHomogeneous fieldCharge c)
    (hd : DerivativeOrderLE p (2*(m:ℤ)-2)) :
    HasJetReduction m d c (2*(m:ℤ)-2) p := by
  obtain ⟨k,hk⟩ := exists_jetOrderLE p
  exact hasJetReduction_of_jetOrder m hm d c _ le_rfl k p hk hw hc hd

end NLS.DifferentialPolynomial
