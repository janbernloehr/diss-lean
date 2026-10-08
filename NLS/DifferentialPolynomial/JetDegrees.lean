import NLS.DifferentialPolynomial.JetAlgebra

/-! # The gradings used in Appendix H

Total weight counts each field and each derivative once. Charge counts second
fields minus first fields. Derivative order counts derivatives across the
whole monomial, rather than only the largest jet index.
-/
noncomputable section
open MvPolynomial
namespace NLS.DifferentialPolynomial

def totalWeight (v : Jet) : ℤ := v.2+1
def fieldCharge (v : Jet) : ℤ := if v.1 then 1 else -1
def derivativeWeight (v : Jet) : ℤ := v.2

/-- The total number of derivatives in every nonzero monomial is at most d. -/
def DerivativeOrderLE (p : Polynomial) (d : ℤ) : Prop :=
  Supported (fun m => Finsupp.weight derivativeWeight m ≤ d) p

namespace DerivativeOrderLE
variable {p q : Polynomial} {d e : ℤ}

theorem zero (d : ℤ) : DerivativeOrderLE 0 d := Supported.zero

theorem mono (hp : DerivativeOrderLE p d) (h : d ≤ e) : DerivativeOrderLE p e :=
  Supported.mono hp (fun _ hm => hm.trans h)

theorem X (v : Jet) : DerivativeOrderLE (MvPolynomial.X v) v.2 :=
  Supported.X _ (by change Finsupp.weight derivativeWeight (Finsupp.single v 1) ≤ (v.2 : ℤ); simp only [Finsupp.weight_single,one_nsmul,derivativeWeight]; exact le_rfl)

theorem neg (hp : DerivativeOrderLE p d) : DerivativeOrderLE (-p) d := Supported.neg hp

theorem add (hp : DerivativeOrderLE p d) (hq : DerivativeOrderLE q d) :
    DerivativeOrderLE (p+q) d := Supported.add hp hq

theorem mul (hp : DerivativeOrderLE p d) (hq : DerivativeOrderLE q e) :
    DerivativeOrderLE (p*q) (d+e) :=
  Supported.mul hp hq (fun a b ha hb => by rw [map_add]; exact add_le_add ha hb)

theorem sum {ι : Type*} (S : Finset ι) (f : ι → Polynomial)
    (hf : ∀ i ∈ S, DerivativeOrderLE (f i) d) : DerivativeOrderLE (∑ i ∈ S, f i) d :=
  Supported.sum S f hf

theorem spatialDerivative (hp : DerivativeOrderLE p d) :
    DerivativeOrderLE (DifferentialPolynomial.spatialDerivative p) (d+1) :=
  Supported.spatialDerivative hp (fun m hm v hv => by
    rw [weight_spatial_shift derivativeWeight 1 (fun _ => by simp [derivativeWeight,nextJet]) m v hv]
    omega)
/-- A bound on total derivatives also bounds every jet occurring in a monomial. -/
theorem jet_order (hp : DerivativeOrderLE p d) (m : Monomial) (hm : m ∈ p.support)
    (v : Jet) (hv : v ∈ m.support) : (v.2 : ℤ) ≤ d := by
  have hmv : 1 ≤ (m v : ℤ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv)
  have hnonneg (w : Jet) (_ : w ∈ m.support) : 0 ≤ (m w : ℤ)*(w.2 : ℤ) :=
    mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  have hterm := Finset.single_le_sum hnonneg hv
  have hweight := hp m hm
  simp only [Finsupp.weight_apply,Finsupp.sum,derivativeWeight,nsmul_eq_mul] at hweight
  have hvn : 0 ≤ (v.2 : ℤ) := Int.natCast_nonneg _
  nlinarith

end DerivativeOrderLE

theorem totalWeight_spatialDerivative {p : Polynomial} {d : ℤ}
    (hp : p.IsWeightedHomogeneous totalWeight d) :
    (spatialDerivative p).IsWeightedHomogeneous totalWeight (d+1) :=
  homogeneous_spatialDerivative _ 1 d (fun _ => by simp [totalWeight,nextJet]) hp

theorem fieldCharge_spatialDerivative {p : Polynomial} {d : ℤ}
    (hp : p.IsWeightedHomogeneous fieldCharge d) :
    (spatialDerivative p).IsWeightedHomogeneous fieldCharge d := by
  simpa using homogeneous_spatialDerivative _ 0 d (fun _ => by simp only [fieldCharge,nextJet,add_zero]; rfl) hp

end NLS.DifferentialPolynomial
