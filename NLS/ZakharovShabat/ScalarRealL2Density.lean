import NLS.ZakharovShabat.Domain
import NLS.SequenceSpaces.FourierTail

/-! # Physical real H¹ density in the original scalar L² space

Symmetric finite Fourier sums preserve conjugate reflection and converge
in the original L² norm. Continuous identities on the real H¹ subspace
therefore extend to the entire physical real L² form.
-/
noncomputable section
open Set Complex Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat

def scalarL2H1Approx (a : Coeff 2) (N : ℕ) : ScalarDomain 2 :=
  ∑ n ∈ Coeff.lowFrequencies N, scalarMode n (a n)

theorem scalarInclusion_scalarL2H1Approx (a : Coeff 2) (N : ℕ) :
    scalarInclusion (scalarL2H1Approx a N) = Coeff.truncate (Coeff.lowFrequencies N) a := by
  simp only [scalarL2H1Approx,map_sum,scalarInclusion_scalarMode,Coeff.truncate]

theorem scalarL2H1Approx_coefficient (a : Coeff 2) (N : ℕ) (j : ℤ) :
    (scalarL2H1Approx a N).val j = if j.natAbs < N then a j else 0 := by
  have h := congrArg (fun b : Coeff 2 => b j) (scalarInclusion_scalarL2H1Approx a N)
  simpa only [scalarInclusion_apply,Coeff.truncate_apply,Coeff.mem_lowFrequencies] using h

theorem scalarL2H1Approx_real (a : Coeff 2) (ha : ∀ j, a j = conj (a (-j))) (N : ℕ) :
    ∀ j, (scalarL2H1Approx a N).val j = conj ((scalarL2H1Approx a N).val (-j)) := by
  intro j
  rw [scalarL2H1Approx_coefficient,scalarL2H1Approx_coefficient,Int.natAbs_neg]
  split_ifs
  · exact ha j
  · exact (map_zero _).symm

theorem tendsto_scalarInclusion_scalarL2H1Approx (a : Coeff 2) :
    Tendsto (fun N : ℕ => scalarInclusion (scalarL2H1Approx a N)) atTop (𝓝 a) := by
  have ht : Tendsto Coeff.lowFrequencies atTop atTop :=
    Filter.tendsto_atTop_finset_of_monotone
      (by intro N M hNM n hn; simp only [Coeff.mem_lowFrequencies] at *; omega)
      (fun n => ⟨n.natAbs+1,by simp⟩)
  simpa only [scalarInclusion_scalarL2H1Approx,Function.comp_def] using!
    (Coeff.tendsto_truncate (by simp) a).comp ht

theorem realL2_eq_of_realH1_agreement (F G : Coeff 2 → ℂ)
    (he : ∀ (a : ScalarDomain 2) (_ha : ∀ j, a.val j = conj (a.val (-j))),
      F (scalarInclusion a) = G (scalarInclusion a))
    (b : Coeff 2) (hb : ∀ j, b j = conj (b (-j)))
    (hF : ContinuousAt F b) (hG : ContinuousAt G b) : F b = G b := by
  have ht := tendsto_scalarInclusion_scalarL2H1Approx b
  have hf := hF.tendsto.comp ht
  have hg := hG.tendsto.comp ht
  exact tendsto_nhds_unique hf (hg.congr (fun N =>
    (he (scalarL2H1Approx b N) (scalarL2H1Approx_real b hb N)).symm))

end NLS.ZakharovShabat
