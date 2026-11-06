import NLS.SequenceSpaces.PeriodOneMiuraTameProduct
import NLS.SequenceSpaces.PeriodOneMiuraShift
import NLS.SequenceSpaces.WeightedFiniteCoefficients

/-! # Exact Sobolev regularity of every actual L2 Miura lift

The literal equation q=u'+u²-c gives q in H^s exactly when u is in
H^(s+1), for every s>=-1. A fractional-loss product bound bootstraps
arbitrary L2 lifts, without a smallness, reality or all-orders hypothesis.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS

/-- Decreasing the Sobolev order preserves the raw weighted L2 criterion. -/
theorem memlp_sobolev_of_le {s t : ℝ} (h : t ≤ s) {f : ℤ → ℂ}
    (hf : Memℓp (fun n => (Weight.sobolev s n : ℂ)*f n) 2) :
    Memℓp (fun n => (Weight.sobolev t n : ℂ)*f n) 2 := by
  apply hf.norm.mono
  intro n
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Weight.positive _ n)]
  exact mul_le_mul_of_nonneg_right (Weight.sobolev_mono h n) (norm_nonneg _)

/-- One finite Sobolev order of a lift gives the exact one-lower order of
its actual distributional Miura image, including negative target orders. -/
theorem periodOneMiura_image_mem_sobolev_of_lift
    (q : PeriodOneHminusOne) (u : Coeff 2) (c : ℂ)
    (himage : periodOneMiura u=q+periodOneL2Inclusion (lp.single 2 0 c))
    (t : ℝ) (ht : 0 ≤ t)
    (hu : Memℓp (fun n => (Weight.sobolev t n : ℂ)*u n) 2) :
    Memℓp (fun n => (Weight.sobolev (t-1) n : ℂ)*q.val n) 2 := by
  let a : WeightedCoeff (Weight.sobolev t) 2 := ⟨u,hu⟩
  let d := WeightedCoeff.sobolevDerivative (t-1)
    (WeightedCoeff.sobolevInclusion (by linarith : (t-1)+1 ≤ t) a)
  let b : WeightedCoeff (Weight.sobolev (t-1)) 2 :=
    ⟨(periodOneMiuraProduct u u).val,periodOneMiuraProduct_mem_sobolev_sub_one t ht u u hu hu⟩
  let Q : WeightedCoeff (Weight.sobolev (t-1)) 2 := (2 : ℂ) • d+b-
    WeightedCoeff.ofFinsupp (Weight.sobolev (t-1)) 2 (Finsupp.single 0 c)
  have heq : Q.val=q.val := by
    funext n
    have he := congrArg (fun p : PeriodOneHminusOne => p.val n) himage
    rw [WeightedCoeff.add_val,periodOneMiura_apply,periodOneL2Inclusion_apply] at he
    change 2*(WeightedCoeff.sobolevDerivative (t-1)
      (WeightedCoeff.sobolevInclusion _ a)).val n+(periodOneMiuraProduct u u).val n-
      (WeightedCoeff.ofFinsupp (Weight.sobolev (t-1)) 2 (Finsupp.single 0 c)).val n=q.val n
    rw [WeightedCoeff.sobolevDerivative_apply,WeightedCoeff.sobolevInclusion_apply,
      periodOneMiuraProduct_apply,WeightedCoeff.ofFinsupp_apply]
    change 2*(I*(Real.pi : ℂ)*n*u n)+(∑' j : ℤ, u (n-j)*u j)-
      (Finsupp.single 0 c) n=q.val n
    simp only [lp.single_apply,Pi.single_apply,Finsupp.single_apply,
      show 0=n ↔ n=0 from eq_comm] at he ⊢
    linear_combination he
  rw [← heq]
  exact Q.property

/-- A quarter-order bootstrap for every actual L2 Miura lift. -/
theorem periodOneMiura_lift_sobolev_step
    (q : PeriodOneHminusOne) (u : Coeff 2) (c : ℂ)
    (himage : periodOneMiura u=q+periodOneL2Inclusion (lp.single 2 0 c))
    (s : ℝ) (hq : Memℓp (fun n => (Weight.sobolev s n : ℂ)*q.val n) 2)
    (t : ℝ) (ht : 0 ≤ t) (hu : Memℓp (fun n => (Weight.sobolev t n : ℂ)*u n) 2)
    (r : ℝ) (hrs : r ≤ s+1) (hrt : r ≤ t+1/4) :
    Memℓp (fun n => (Weight.sobolev r n : ℂ)*u n) 2 := by
  have hp := memlp_sobolev_of_le (by linarith : r-1 ≤ t-3/4)
    (periodOneMiuraProduct_mem_sobolev_sub t ht (3/4) (by norm_num) u u hu hu)
  have hq' := memlp_sobolev_of_le (by linarith : r-1 ≤ s) hq
  have hu' := memlp_sobolev_of_le (by linarith : r-1 ≤ t) hu
  have hc : Memℓp (fun n => (Weight.sobolev (r-1) n : ℂ)*(lp.single 2 0 c : Coeff 2) n) 2 := by
    have H := (WeightedCoeff.ofFinsupp (Weight.sobolev (r-1)) 2 (Finsupp.single 0 c)).property
    change Memℓp (fun n => (Weight.sobolev (r-1) n : ℂ)*
      (WeightedCoeff.ofFinsupp (Weight.sobolev (r-1)) 2 (Finsupp.single 0 c)).val n) 2 at H
    simpa only [WeightedCoeff.ofFinsupp_apply,lp.single_apply,Pi.single_apply,
      Finsupp.single_apply,show ∀ n : ℤ, (0=n ↔ n=0) from fun _ => eq_comm] using H
  have hder (n : ℤ) : I*(Real.pi : ℂ)*n*u n=
      (1/2 : ℂ)*(q.val n+(lp.single 2 0 c : Coeff 2) n-(periodOneMiuraProduct u u).val n) := by
    have he := congrArg (fun p : PeriodOneHminusOne => p.val n) himage
    rw [WeightedCoeff.add_val,periodOneMiura_apply,periodOneL2Inclusion_apply] at he
    rw [periodOneMiuraProduct_apply]
    linear_combination (1/2 : ℂ)*he
  have hd : Memℓp (fun n => (Weight.sobolev (r-1) n : ℂ)*(I*(Real.pi : ℂ)*n*u n)) 2 := by
    have heq : (fun n => (Weight.sobolev (r-1) n : ℂ)*(I*(Real.pi : ℂ)*n*u n))=
        (fun n => (1/2 : ℂ)*((Weight.sobolev (r-1) n : ℂ)*q.val n+
          (Weight.sobolev (r-1) n : ℂ)*(lp.single 2 0 c : Coeff 2) n-
          (Weight.sobolev (r-1) n : ℂ)*(periodOneMiuraProduct u u).val n)) := by
      funext n
      rw [hder]
      ring
    rw [heq]
    exact ((hq'.add hc).sub hp).const_mul (1/2 : ℂ)
  have H := WeightedCoeff.memlp_sobolev_succ_of_derivative (r-1) hu' hd
  simpa only [sub_add_cancel] using H

/-- EVERY actual L2 lift of an H^s Miura image is H^(s+1), for ALL s>=-1.
The starting L2 lift may be arbitrary; no all-orders or smallness assumption. -/
theorem periodOneMiura_lift_mem_sobolev_of_image
    (q : PeriodOneHminusOne) (u : Coeff 2) (c : ℂ)
    (himage : periodOneMiura u=q+periodOneL2Inclusion (lp.single 2 0 c))
    (s : ℝ) (hs : -1 ≤ s)
    (hq : Memℓp (fun n => (Weight.sobolev s n : ℂ)*q.val n) 2) :
    Memℓp (fun n => (Weight.sobolev (s+1) n : ℂ)*u n) 2 := by
  have H : ∀ N : ℕ, ∀ r : ℝ, 0 ≤ r → r ≤ (N : ℝ)/4 → r ≤ s+1 →
      Memℓp (fun n => (Weight.sobolev r n : ℂ)*u n) 2 := by
    intro N
    induction N with
    | zero =>
      intro r hr hrN _
      have he : r=0 := by norm_num at hrN; linarith
      simpa only [he,Weight.sobolev_zero_apply,Complex.ofReal_one,one_mul] using lp.memℓp u
    | succ N ih =>
      intro r hr hrN hrs
      let t : ℝ := max 0 (r-1/4)
      have ht : 0 ≤ t := le_max_left _ _
      have htN : t ≤ (N : ℝ)/4 := by
        apply max_le
        · positivity
        · push_cast at hrN
          linarith
      have hts : t ≤ s+1 := by apply max_le <;> linarith
      have hu := ih t ht htN hts
      exact periodOneMiura_lift_sobolev_step q u c himage s hq t ht hu r hrs
        (by dsimp only [t]; linarith [le_max_right (0 : ℝ) (r-1/4)])
  obtain ⟨N,hN⟩ := exists_nat_ge (4*(s+1))
  exact H N (s+1) (by linarith) (by linarith) le_rfl

/-- Exact ALL-order source/lift regularity for the literal shifted Miura equation. -/
theorem periodOneMiura_sobolev_iff
    (q : PeriodOneHminusOne) (u : Coeff 2) (c : ℂ)
    (himage : periodOneMiura u=q+periodOneL2Inclusion (lp.single 2 0 c))
    (s : ℝ) (hs : -1 ≤ s) :
    Memℓp (fun n => (Weight.sobolev s n : ℂ)*q.val n) 2 ↔
      Memℓp (fun n => (Weight.sobolev (s+1) n : ℂ)*u n) 2 := by
  refine ⟨periodOneMiura_lift_mem_sobolev_of_image q u c himage s hs, ?_⟩
  intro hu
  have h := periodOneMiura_image_mem_sobolev_of_lift q u c himage (s+1) (by linarith) hu
  simpa only [add_sub_cancel_right] using h

end NLS
