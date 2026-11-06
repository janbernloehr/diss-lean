import NLS.SequenceSpaces.PeriodOneMiuraSobolevEquivalence
import NLS.SequenceSpaces.BoundedScalarProducts

/-! # Exact Sobolev regularity for the actual linearized Miura equation

A given L2 solution of the literal Miura Jacobian equation gains the full
requested order. The fixed coefficient needs only that same finite order.
The fractional product estimate gives a quarter-order bootstrap.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS

/-- The actual shifted lift has the same all-order regularity as the
unshifted energy-translated lift; the constant changes only the zero mode. -/
theorem periodOneShiftedMiura_lift_mem_sobolev
    (m : ℕ) (q : PeriodOneHminusOne) (v : Coeff 2)
    (hsolve : periodOneShiftedMiura m v=q)
    (s : ℝ) (hs : -1≤s)
    (hq : Memℓp (fun n => (Weight.sobolev s n : ℂ)*q.val n) 2) :
    Memℓp (fun n => (Weight.sobolev (s+1) n : ℂ)*v n) 2 := by
  let c : ℂ := (((m : ℝ)+1 : ℝ)/2 : ℂ)
  let u : Coeff 2 := v+lp.single 2 0 c
  have hi0 := periodOneMiura_shift m v
  rw [hsolve] at hi0
  have hi : periodOneMiura u=q+periodOneL2Inclusion (lp.single 2 0 (c^2)) := hi0
  have hh : Memℓp (fun n => (Weight.sobolev (s+1) n : ℂ)*u n) 2 :=
    periodOneMiura_lift_mem_sobolev_of_image q u (c^2) hi s hs hq
  apply memlp_vector_of_eq_outside_finset (E := ℂ)
    (f := fun n => (Weight.sobolev (s+1) n : ℂ)*v n) hh {0}
  intro n hn
  have hn0 : n≠0 := by simpa only [Finset.mem_singleton] using hn
  simp only [u,lp.coeFn_add,Pi.add_apply,lp.single_apply,Pi.single_apply,if_neg hn0,add_zero]

/-- A quarter-order gain for every L2 solution of the ACTUAL shifted
Miura Jacobian equation, with a fixed coefficient of the requested order. -/
theorem periodOneMiura_linearized_sobolev_step
    (m : ℕ) (u v : Coeff 2) (f : PeriodOneHminusOne)
    (he : ∀ n : ℤ, periodOneMassSymbol m n*v n+
      2*(periodOneMiuraProduct u v).val n=f.val n)
    (s : ℝ) (hu : Memℓp (fun n => (Weight.sobolev (s+1) n : ℂ)*u n) 2)
    (hf : Memℓp (fun n => (Weight.sobolev s n : ℂ)*f.val n) 2)
    (t : ℝ) (ht : 0≤t) (hts : t≤s+1)
    (hv : Memℓp (fun n => (Weight.sobolev t n : ℂ)*v n) 2)
    (r : ℝ) (hrs : r≤s+1) (hrt : r≤t+1/4) :
    Memℓp (fun n => (Weight.sobolev r n : ℂ)*v n) 2 := by
  have hu' := memlp_sobolev_of_le hts hu
  have hp := memlp_sobolev_of_le (by linarith : r-1≤t-3/4)
    (periodOneMiuraProduct_mem_sobolev_sub t ht (3/4) (by norm_num) u v hu' hv)
  have hf' := memlp_sobolev_of_le (by linarith : r-1≤s) hf
  have hv' := memlp_sobolev_of_le (by linarith : r-1≤t) hv
  let a : ℂ := (((m : ℝ)+1 : ℝ) : ℂ)
  have hder (n : ℤ) : I*(Real.pi : ℂ)*n*v n=
      (1/2 : ℂ)*(f.val n-a*v n-2*(periodOneMiuraProduct u v).val n) := by
    have h := he n
    simp only [periodOneMassSymbol,ofReal_add,ofReal_one] at h
    dsimp only [a]
    push_cast
    linear_combination (1/2 : ℂ)*h
  have hd : Memℓp (fun n => (Weight.sobolev (r-1) n : ℂ)*(I*(Real.pi : ℂ)*n*v n)) 2 := by
    have heq : (fun n => (Weight.sobolev (r-1) n : ℂ)*(I*(Real.pi : ℂ)*n*v n))=
        (fun n => (1/2 : ℂ)*((Weight.sobolev (r-1) n : ℂ)*f.val n-
          a*((Weight.sobolev (r-1) n : ℂ)*v n)-
          2*((Weight.sobolev (r-1) n : ℂ)*(periodOneMiuraProduct u v).val n))) := by
      funext n
      rw [hder]
      ring
    rw [heq]
    exact ((hf'.sub (hv'.const_mul a)).sub (hp.const_mul (2 : ℂ))).const_mul (1/2 : ℂ)
  have H := WeightedCoeff.memlp_sobolev_succ_of_derivative (r-1) hv' hd
  simpa only [sub_add_cancel] using H

/-- EVERY actual L2 solution of the literal Miura Jacobian equation has
H^(s+1) regularity when its coefficient is H^(s+1) and its image is H^s,
for EVERY real s>=-1. No greater coefficient order or smallness is needed. -/
theorem periodOneMiura_linearized_lift_mem_sobolev
    (m : ℕ) (u v : Coeff 2) (f : PeriodOneHminusOne)
    (he : ∀ n : ℤ, periodOneMassSymbol m n*v n+
      2*(periodOneMiuraProduct u v).val n=f.val n)
    (s : ℝ) (hs : -1≤s)
    (hu : Memℓp (fun n => (Weight.sobolev (s+1) n : ℂ)*u n) 2)
    (hf : Memℓp (fun n => (Weight.sobolev s n : ℂ)*f.val n) 2) :
    Memℓp (fun n => (Weight.sobolev (s+1) n : ℂ)*v n) 2 := by
  have H : ∀ N : ℕ, ∀ r : ℝ, 0≤r → r≤(N : ℝ)/4 → r≤s+1 →
      Memℓp (fun n => (Weight.sobolev r n : ℂ)*v n) 2 := by
    intro N
    induction N with
    | zero =>
      intro r hr hrN _
      have h0 : r=0 := by norm_num at hrN; linarith
      simpa only [h0,Weight.sobolev_zero_apply,ofReal_one,one_mul] using lp.memℓp v
    | succ N ih =>
      intro r hr hrN hrs
      let t : ℝ := max 0 (r-1/4)
      have ht : 0≤t := le_max_left _ _
      have htN : t≤(N : ℝ)/4 := by
        apply max_le
        · positivity
        · push_cast at hrN
          linarith
      have hts : t≤s+1 := by apply max_le <;> linarith
      exact periodOneMiura_linearized_sobolev_step m u v f he s hu hf t ht hts
        (ih t ht htN hts) r hrs (by dsimp only [t]; linarith [le_max_right (0 : ℝ) (r-1/4)])
  obtain ⟨N,hN⟩ := exists_nat_ge (4*(s+1))
  exact H N (s+1) (by linarith) (by linarith) le_rfl

end NLS
