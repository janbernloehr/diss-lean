import NLS.KdV.HillDirichletFilledQuotient
import NLS.KdV.HillDiscriminantJointCotangent
import NLS.KdV.HminusOneCanonicalDirichletMultiplicity

/-! The mixed spectral bracket after filling its removable energy
pole, its resonant normalization, and its values on all labelled
Dirichlet energies. All statements hold on the whole complex domain. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.KdV

theorem continuous_hillHminus_discriminant_Dirichlet_bracket_energy
    (n : ℕ+) (q : PeriodOneHminusOne) :
    Continuous (fun E : ℂ => NLS.Poisson.hminusGardnerBracket
      (fun p => hillHminusDiscriminant p E) (hillHminusCanonicalDirichlet n) q) := by
  let M : PeriodOneHminusOne →L[ℂ] ℂ := fderiv ℂ (hillHminusCanonicalDirichlet n) q
  let B : (PeriodOneHminusOne →L[ℂ] ℂ) →L[ℂ] ℂ := NLS.Poisson.gardnerCotangentBivector.flip M
  have hc := B.continuous.comp (analyticOnNhd_hillHminusDiscriminantCotangent_energy q).continuous
  exact hc

theorem hillHminus_filled_discriminant_Dirichlet_Gardner
    (n : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ hillHminusCanonicalDirichletDomain) (E : ℂ) :
    2*deriv (hillHminusDirichlet q) (hillHminusCanonicalDirichlet n q)*
      NLS.Poisson.hminusGardnerBracket (fun p => hillHminusDiscriminant p E) (hillHminusCanonicalDirichlet n) q=
      -hillHminusDirichletFilledQuotient n (E,q)*hillHminusDirichletSheet n q := by
  have hQ : AnalyticOnNhd ℂ (fun z => hillHminusDirichletFilledQuotient n (z,q)) univ := by
    intro z _
    exact (analyticOnNhd_hillHminusDirichletFilledQuotient n (z,q) ⟨mem_univ _,hq⟩).comp
      (f := fun w : ℂ => (w,q)) (analyticAt_id.prod analyticAt_const)
  have hf : Continuous (fun z : ℂ =>
      2*deriv (hillHminusDirichlet q) (hillHminusCanonicalDirichlet n q)*
        NLS.Poisson.hminusGardnerBracket (fun p => hillHminusDiscriminant p z) (hillHminusCanonicalDirichlet n) q) :=
    continuous_const.mul (continuous_hillHminus_discriminant_Dirichlet_bracket_energy n q)
  have hg : Continuous (fun z : ℂ => -hillHminusDirichletFilledQuotient n (z,q)*hillHminusDirichletSheet n q) :=
    hQ.continuous.neg.mul continuous_const
  have he := Continuous.ext_on (s := ({hillHminusCanonicalDirichlet n q} : Set ℂ)ᶜ)
    (dense_compl_singleton (hillHminusCanonicalDirichlet n q)) hf hg (fun z hz => ?_)
  · exact congrFun he E
  · have hn : z-hillHminusCanonicalDirichlet n q ≠ 0 := sub_ne_zero.mpr (by simpa using hz)
    have hm := hillHminus_discriminant_Dirichlet_Gardner n z q hq
    rw [← hillHminusDirichletFilledQuotient_factor n q hq z] at hm
    apply mul_left_cancel₀ hn
    linear_combination hm


theorem hillHminus_resonant_discriminant_Dirichlet_Gardner
    (n : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ hillHminusCanonicalDirichletDomain) :
    2*NLS.Poisson.hminusGardnerBracket (fun p => hillHminusDiscriminant p (hillHminusCanonicalDirichlet n q))
      (hillHminusCanonicalDirichlet n) q= -hillHminusDirichletSheet n q := by
  have hm := hillHminus_filled_discriminant_Dirichlet_Gardner n q hq (hillHminusCanonicalDirichlet n q)
  rw [hillHminusDirichletFilledQuotient_at_root] at hm
  apply mul_left_cancel₀ (deriv_hillHminusCanonicalDirichlet_ne_zero n q hq)
  linear_combination hm

theorem hillHminus_discriminant_at_Dirichlet_Gardner_matrix
    (n m : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ hillHminusCanonicalDirichletDomain) :
    NLS.Poisson.hminusGardnerBracket (fun p => hillHminusDiscriminant p (hillHminusCanonicalDirichlet m q))
      (hillHminusCanonicalDirichlet n) q=(if n=m then -hillHminusDirichletSheet n q/2 else 0) := by
  by_cases hnm : n=m
  · subst m
    rw [if_pos rfl]
    linear_combination (1/2:ℂ)*hillHminus_resonant_discriminant_Dirichlet_Gardner n q hq
  · rw [if_neg hnm]
    have hE : hillHminusCanonicalDirichlet m q ≠ hillHminusCanonicalDirichlet n q :=
      fun he => hnm ((injective_hillHminusCanonicalDirichlet q hq he).symm)
    have hQ : hillHminusDirichletFilledQuotient n (hillHminusCanonicalDirichlet m q,q)=0 := by
      rw [hillHminusDirichletFilledQuotient_off_root n q hq _ hE,
        hillHminusCanonicalDirichlet_is_root m q hq,zero_div]
    have hm := hillHminus_filled_discriminant_Dirichlet_Gardner n q hq (hillHminusCanonicalDirichlet m q)
    rw [hQ,neg_zero,zero_mul] at hm
    exact (mul_eq_zero.mp hm).resolve_left
      (mul_ne_zero (by norm_num) (deriv_hillHminusCanonicalDirichlet_ne_zero n q hq))

end NLS.KdV
