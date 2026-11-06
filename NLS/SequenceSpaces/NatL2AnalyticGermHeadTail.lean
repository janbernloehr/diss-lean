import NLS.SequenceSpaces.NatL2HeadTailAssembly

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate Classical

namespace NLS.Coeff



/-- A bounded analytic head and Hilbert tail matching a real-parameter
sequence yield a genuine complex Hilbert analytic germ of that sequence. -/
theorem exists_natL2_analytic_germ_of_head_tail_matching
    {E R : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace R]
    (ι : R → E) (hι : Continuous ι) (r0 : R)
    (S : R → lp (fun _ : ℕ => ℂ) 2)
    (U : Set E) (hU : IsOpen U) (hr0 : ι r0∈U)
    (K : ℕ) (a : E → ℕ → ℂ) (T : E → Coeff 2)
    (ha : ∀ k<K, AnalyticOnNhd ℂ (fun x => a x k) U)
    (hT : AnalyticOnNhd ℂ T U) (b : ℕ → ℝ) (M : ℝ)
    (hab : ∀ x∈U, ∀ k<K, ‖a x k‖≤b k)
    (hTb : ∀ x∈U, ‖T x‖^2≤M)
    (hhead : ∀ᶠ r in 𝓝 r0, ∀ k<K, a (ι r) k=S r k)
    (htail : ∀ᶠ r in 𝓝 r0, ∀ k : ℕ, T (ι r) (Equiv.intEquivNat.symm k)=S r (k+K)) :
    ∃ F : E → lp (fun _ : ℕ => ℂ) 2, AnalyticAt ℂ F (ι r0) ∧
      ∀ᶠ r in 𝓝 r0, F (ι r)=S r := by
  obtain ⟨F,hFa,_,hcoord⟩ := exists_natL2_analytic_head_tail U hU K a T ha hT b M hab hTb
  have hnear : ∀ᶠ r in 𝓝 r0, ι r∈U := hι.continuousAt.preimage_mem_nhds (hU.mem_nhds hr0)
  refine ⟨F,hFa _ hr0,?_⟩
  filter_upwards [hnear,hhead,htail] with r hr hh ht
  ext k
  rw [hcoord (ι r) hr k]
  by_cases hk : k<K
  · rw [if_pos hk]
    exact hh k hk
  · rw [if_neg hk,ht (k-K)]
    exact congrArg (fun j : ℕ => S r j) (Nat.sub_add_cancel (not_lt.mp hk))

end NLS.Coeff
