import NLS.ComplexAnalysis.FinitePoleRemoval

/-! # Removing simple poles of an analytic quotient

At a simple zero of the denominator, the principal coefficient is the
numerator value divided by the denominator derivative. Subtracting the
finite collection of these principal parts gives an analytic normal
form on any set containing no other denominator zeros.
-/

noncomputable section
open Set Filter Topology
namespace NLS.ComplexAnalysis

/-- An analytic germ has an analytic divided difference at its base point. -/
theorem analyticAt_dslope_same {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) :
    AnalyticAt ℂ (dslope f a) a := by
  obtain ⟨p,hp⟩ := hf
  exact ⟨p.fslope,hp.has_fpower_series_dslope_fslope⟩

/-- The residue of a quotient at a simple denominator zero is exact,
and removing it leaves an analytic germ. -/
theorem exists_analytic_simpleQuotient_remainder {f g : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a) (hg : AnalyticAt ℂ g a)
    (hzero : g a = 0) (hsimple : deriv g a ≠ 0) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q a ∧
      (fun z => f z/g z) =ᶠ[𝓝[≠] a] (fun z => (f a/deriv g a)/(z-a)+q z) := by
  let u := dslope g a
  have hu : AnalyticAt ℂ u a := analyticAt_dslope_same hg
  have hua : u a = deriv g a := dslope_same g a
  have hune : u a ≠ 0 := hua ▸ hsimple
  let v : ℂ → ℂ := fun z => f z/u z
  have hv : AnalyticAt ℂ v a := hf.div hu hune
  refine ⟨dslope v a,analyticAt_dslope_same hv,?_⟩
  filter_upwards [(hu.continuousAt.eventually_ne hune).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z huz hza
  have hza' : z ≠ a := hza
  have hsub : z-a ≠ 0 := sub_ne_zero.mpr hza'
  have huzform : u z = (g z-g a)/(z-a) := by
    dsimp only [u]
    rw [dslope_of_ne g hza',slope_def_field]
  have hgform : g z = (z-a)*u z := by
    rw [huzform,hzero,sub_zero]
    field_simp
  rw [dslope_of_ne v hza',slope_def_field]
  change f z/g z = (f a/deriv g a)/(z-a)+(f z/u z-f a/u a)/(z-a)
  rw [hua,hgform]
  field_simp [hsub,huz,hsimple]
  ring

/-- The literal finite principal parts of a quotient with simple poles. -/
def simpleQuotientPrincipalParts (f g : ℂ → ℂ) (s : Finset ℂ) (z : ℂ) : ℂ :=
  ∑ a ∈ s, (f a/deriv g a)/(z-a)

theorem analyticAt_simpleQuotientPrincipalParts (f g : ℂ → ℂ) (s : Finset ℂ)
    {z : ℂ} (hz : z ∉ s) :
    AnalyticAt ℂ (simpleQuotientPrincipalParts f g s) z := by
  unfold simpleQuotientPrincipalParts
  apply Finset.analyticAt_fun_sum s
  intro a ha
  exact analyticAt_const.div (analyticAt_id.sub analyticAt_const)
    (sub_ne_zero.mpr (by rintro rfl; exact hz ha))

theorem meromorphicOn_simpleQuotient_remainder {f g : ℂ → ℂ} {K : Set ℂ}
    (hf : AnalyticOnNhd ℂ f K) (hg : AnalyticOnNhd ℂ g K) (s : Finset ℂ) :
    MeromorphicOn (fun z => f z/g z-simpleQuotientPrincipalParts f g s z) K := by
  intro z hz
  apply ((hf z hz).meromorphicAt.div (hg z hz).meromorphicAt).sub
  unfold simpleQuotientPrincipalParts
  apply MeromorphicAt.fun_sum
  intro a _
  exact (MeromorphicAt.const _ _).div ((analyticAt_id.sub analyticAt_const).meromorphicAt)

/-- Removing all simple denominator zeros in a set produces an analytic
filled remainder; the residues are derived rather than supplied. -/
theorem analyticOnNhd_simpleQuotient_remainder {f g : ℂ → ℂ} {K : Set ℂ}
    (hf : AnalyticOnNhd ℂ f K) (hg : AnalyticOnNhd ℂ g K) (s : Finset ℂ)
    (hzero : ∀ a ∈ s, g a = 0) (hsimple : ∀ a ∈ s, deriv g a ≠ 0)
    (hcover : ∀ z ∈ K, g z = 0 → z ∈ s) :
    AnalyticOnNhd ℂ (toMeromorphicNFOn
      (fun z => f z/g z-simpleQuotientPrincipalParts f g s z) K) K := by
  intro a ha
  have hm := meromorphicOn_simpleQuotient_remainder hf hg s
  by_cases has : a ∈ s
  · obtain ⟨q,hq,he⟩ := exists_analytic_simpleQuotient_remainder
      (hf a ha) (hg a ha) (hzero a has) (hsimple a has)
    have hs := analyticAt_simpleQuotientPrincipalParts f g (s.erase a) (Finset.notMem_erase _ _)
    apply analyticAt_normalForm_of_punctured_eq hm ha (hq.sub hs)
    filter_upwards [he] with z hz
    have hsplit : simpleQuotientPrincipalParts f g s z =
        (f a/deriv g a)/(z-a)+simpleQuotientPrincipalParts f g (s.erase a) z :=
      (Finset.add_sum_erase s (fun b => (f b/deriv g b)/(z-b)) has).symm
    rw [hz,hsplit]
    simp only [Pi.sub_apply]
    ring
  · have hga : g a ≠ 0 := fun he => has (hcover a ha he)
    have hq := ((hf a ha).div (hg a ha) hga).sub
      (analyticAt_simpleQuotientPrincipalParts f g s has)
    exact analyticAt_normalForm_of_punctured_eq hm ha hq (Filter.EventuallyEq.refl _ _)

/-- Away from the poles the filled remainder is the original quotient
minus the literal principal-part sum. -/
theorem simpleQuotient_remainder_normalForm_eq {f g : ℂ → ℂ} {K : Set ℂ}
    (hf : AnalyticOnNhd ℂ f K) (hg : AnalyticOnNhd ℂ g K) (s : Finset ℂ)
    {z : ℂ} (hz : z ∈ K) (hzs : z ∉ s) (hgz : g z ≠ 0) :
    toMeromorphicNFOn (fun w => f w/g w-simpleQuotientPrincipalParts f g s w) K z =
      f z/g z-simpleQuotientPrincipalParts f g s z := by
  rw [toMeromorphicNFOn_eq_toMeromorphicNFAt (meromorphicOn_simpleQuotient_remainder hf hg s) hz]
  have ha := ((hf z hz).div (hg z hz) hgz).sub (analyticAt_simpleQuotientPrincipalParts f g s hzs)
  exact congrFun (toMeromorphicNFAt_eq_self.mpr ha.meromorphicNFAt) z

end NLS.ComplexAnalysis
