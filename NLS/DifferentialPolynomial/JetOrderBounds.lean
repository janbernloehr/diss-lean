import NLS.DifferentialPolynomial.JetDegrees

/-! # Bounds on individual jets

These bounds are separate from the total derivative count of a monomial.
They are used to terminate integration by parts at a prescribed jet order.
-/
noncomputable section
open MvPolynomial
namespace NLS.DifferentialPolynomial

def JetOrderLE (p : Polynomial) (k : ℕ) : Prop :=
  Supported (fun m => ∀ v ∈ m.support, v.2 ≤ k) p

namespace JetOrderLE
variable {p q : Polynomial} {k l : ℕ}

theorem zero (k : ℕ) : JetOrderLE 0 k := Supported.zero

theorem mono (hp : JetOrderLE p k) (h : k ≤ l) : JetOrderLE p l :=
  Supported.mono hp (fun _ hm v hv => (hm v hv).trans h)

theorem add (hp : JetOrderLE p k) (hq : JetOrderLE q k) : JetOrderLE (p+q) k :=
  Supported.add hp hq

theorem neg (hp : JetOrderLE p k) : JetOrderLE (-p) k := Supported.neg hp

theorem sum {ι : Type*} (S : Finset ι) (f : ι → Polynomial)
    (hf : ∀ i ∈ S, JetOrderLE (f i) k) : JetOrderLE (∑ i ∈ S, f i) k :=
  Supported.sum S f hf

theorem X (v : Jet) : JetOrderLE (MvPolynomial.X v) v.2 := by
  apply Supported.X
  intro w hw
  have he : w = v := by simpa using hw
  simpa only [he] using le_refl v.2

theorem mul (hp : JetOrderLE p k) (hq : JetOrderLE q k) : JetOrderLE (p*q) k := by
  change Supported (fun m => ∀ v ∈ m.support, v.2 ≤ k) (p*q)
  apply Supported.mul (R := fun m => ∀ v ∈ m.support, v.2 ≤ k) hp hq
  intro a b ha hb v hv
  rcases Finset.mem_union.mp (Finsupp.support_add hv) with h | h
  · exact ha v h
  · exact hb v h

theorem of_derivativeOrder {d : ℤ} (hp : DerivativeOrderLE p d) (h : d ≤ k) :
    JetOrderLE p k := by
  intro m hm v hv
  have ht := (hp.jet_order m hm v hv).trans h
  exact_mod_cast ht

theorem vars (hp : JetOrderLE p k) (v : Jet) (hv : v ∈ p.vars) : v.2 ≤ k := by
  obtain ⟨m,hm,hvm⟩ := (MvPolynomial.mem_vars_iff_mem_support v).mp hv
  exact hp m hm v hvm
end JetOrderLE

/-- Every polynomial has a finite bound on its individual jet orders. -/
theorem exists_jetOrderLE (p : Polynomial) : ∃ k, JetOrderLE p k := by
  classical
  refine ⟨p.vars.sup Prod.snd,?_⟩
  intro m hm v hv
  exact Finset.le_sup ((MvPolynomial.mem_vars_iff_mem_support v).mpr ⟨m,hm,hv⟩)

/-- Removing one occurrence of a jet subtracts exactly its contribution
from any additive monomial grading. -/
theorem weight_erase_one (w : Jet → ℤ) (m : Monomial) (v : Jet) (hv : v ∈ m.support) :
    Finsupp.weight w (m-Finsupp.single v 1) = Finsupp.weight w m-w v := by
  have h := Finsupp.weight_sub_single_add (w := w) (Finsupp.mem_support_iff.mp hv)
  omega

/-- Pull a jet factor out of a monomial, retaining its coefficient. -/
theorem monomial_factor_jet (m : Monomial) (c : ℂ) (v : Jet) (hv : v ∈ m.support) :
    MvPolynomial.monomial m c = X v*MvPolynomial.monomial (m-Finsupp.single v 1) c := by
  rw [MvPolynomial.X,MvPolynomial.monomial_mul,one_mul,add_comm,
    Finsupp.sub_add_single_one_cancel (Finsupp.mem_support_iff.mp hv)]

end NLS.DifferentialPolynomial
