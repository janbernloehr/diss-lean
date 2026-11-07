import NLS.KdV.PeriodOneHamiltonian

/-! Exact original period-one physical kinetic energy of a literal
two-sided Fourier mode, retaining its raw complex amplitude. -/
noncomputable section
open Complex NLS.ZakharovShabat
namespace NLS.KdV

theorem periodOneSobolevKinetic_mode_pair (q : ScalarDomain 2) (n : ℕ+) (c : ℂ)
    (hq : ∀ k : ℤ, q.val k=(if k=(n:ℤ) then c else 0)+(if k=-(n:ℤ) then c else 0)) :
    periodOneSobolevKinetic (q,q)=2*((2*Real.pi*(n:ℕ):ℝ):ℂ)^2*c^2 := by
  have hn : (0:ℤ)<n := by exact_mod_cast n.pos
  have hne : (n:ℤ)≠-(n:ℤ) := by omega
  rw [periodOneSobolevKinetic,Coeff.dualPairing_apply]
  rw [tsum_eq_sum (s := {(n:ℤ),-(n:ℤ)}) (fun k hk => by
    have hk' : k≠(n:ℤ) ∧ k≠-(n:ℤ) := by
      simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using hk
    have hkn := hk'.1
    have hkm := hk'.2
    rw [periodOneDerivative_apply,hq]
    simp only [if_neg hkn,if_neg hkm,zero_add,mul_zero])]
  rw [Finset.sum_insert (a := (n:ℤ)) (s := {-(n:ℤ)}) (by simpa only [Finset.mem_singleton] using hne),Finset.sum_singleton]
  simp only [Coeff.reflection_apply,periodOneDerivative_apply,hq,neg_neg,ite_true,if_neg hne,if_neg (Ne.symm hne),add_zero,zero_add,Int.cast_neg]
  push_cast
  ring_nf
  simp only [I_sq]
  ring

end NLS.KdV
