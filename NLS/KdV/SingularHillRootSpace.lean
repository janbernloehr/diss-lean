import NLS.KdV.SingularHillOperatorDomain
import NLS.FunctionalAnalysis.ResolventRootSpace

/-! # Actual root chains of the original singular Hill operator

Every application uses a representative in the unchanged original H1 domain
inside the original H-minus-one base space. The chain spaces agree exactly
with those of the actual partial operator. Both pencil signs give the same
spaces; no endpoint regularity or semisimplicity assumption is imposed here.
-/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue
open NLS.FunctionalAnalysis

/-- The finite root-chain levels of the actual original singular Hill operator. -/
def singularHillRootSpace (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ) (n : ℕ) :
    Submodule ℂ (FourierLebesgueSpace (2:ℝ) (-1) 2) :=
  pencilRootSpace singularHillDomainInclusion.toLinearMap
    (singularHillOperator q-z • singularHillDomainInclusion).toLinearMap n

/-- Every root chain retains the actual H1 domain at every step. -/
theorem mem_singularHillRootSpace_succ (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (z : ℂ) (n : ℕ) (x : FourierLebesgueSpace (2:ℝ) (-1) 2) :
    x ∈ singularHillRootSpace q z (n+1) ↔
      ∃ f : FourierLebesgueSpace (2:ℝ) 1 2, singularHillDomainInclusion f = x ∧
        singularHillOperator q f-z • singularHillDomainInclusion f ∈ singularHillRootSpace q z n :=
  mem_pencilRootSpace_succ _ _ n x

/-- The full algebraic root space is the union of all actual finite chains. -/
def singularHillRootSpaceTop (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ) :
    Submodule ℂ (FourierLebesgueSpace (2:ℝ) (-1) 2) :=
  pencilRootSpaceTop singularHillDomainInclusion.toLinearMap
    (singularHillOperator q-z • singularHillDomainInclusion).toLinearMap

theorem mem_singularHillRootSpaceTop (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (z : ℂ) (x : FourierLebesgueSpace (2:ℝ) (-1) 2) :
    x ∈ singularHillRootSpaceTop q z ↔ ∃ n : ℕ, x ∈ singularHillRootSpace q z n :=
  mem_pencilRootSpaceTop _ _ x

/-- These are exactly the actual partial operator's root chains in its native spectral-pencil sign. -/
theorem singularHillRootSpace_eq_partial (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (z : ℂ) (n : ℕ) :
    singularHillRootSpace q z n =
      pencilRootSpace (singularHillPartialOperator q).domain.subtype
        (z • (singularHillPartialOperator q).domain.subtype-(singularHillPartialOperator q).toFun) n := by
  let T := singularHillPartialOperator q
  have he := pencilRootSpace_equiv singularHillDomainInclusion.toLinearMap
    (singularHillOperator q-z • singularHillDomainInclusion).toLinearMap
    T.domain.subtype (T.toFun-z • T.domain.subtype) singularHillDomainEquiv
    (LinearEquiv.refl ℂ (FourierLebesgueSpace (2:ℝ) (-1) 2))
    (fun f => singularHillDomainEquiv_val f)
    (fun f => by
      change T (singularHillDomainEquiv f)-z • (singularHillDomainEquiv f).val =
        singularHillOperator q f-z • singularHillDomainInclusion f
      rw [singularHillPartialOperator_apply, singularHillDomainEquiv_val]) n
  have hsign : z • T.domain.subtype-T.toFun = (-1:ℂ) • (T.toFun-z • T.domain.subtype) := by
    ext f
    simp only [LinearMap.sub_apply, LinearMap.smul_apply]
    module
  change singularHillRootSpace q z n = pencilRootSpace T.domain.subtype
    (z • T.domain.subtype-T.toFun) n
  rw [hsign, pencilRootSpace_smul _ _ (-1) (by norm_num)]
  ext x
  exact he x

/-- The complete algebraic root space is that of the unchanged actual partial operator. -/
theorem singularHillRootSpaceTop_eq_partial (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ) :
    singularHillRootSpaceTop q z =
      pencilRootSpaceTop (singularHillPartialOperator q).domain.subtype
        (z • (singularHillPartialOperator q).domain.subtype-(singularHillPartialOperator q).toFun) := by
  unfold singularHillRootSpaceTop pencilRootSpaceTop
  exact iSup_congr (fun n => singularHillRootSpace_eq_partial q z n)

/-- All actual algebraic root vectors still belong to the original operator domain. -/
theorem singularHillRootSpaceTop_le_domain (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ) :
    singularHillRootSpaceTop q z ≤ (singularHillPartialOperator q).domain := by
  intro x hx
  obtain ⟨n,hn⟩ := (mem_singularHillRootSpaceTop q z x).mp hx
  cases n with
  | zero =>
    have hx0 : x = 0 := hn
    rw [hx0]
    exact (singularHillPartialOperator q).domain.zero_mem
  | succ n =>
    obtain ⟨f,hf,_⟩ := (mem_singularHillRootSpace_succ q z n x).mp hn
    exact ⟨f,hf⟩

/-- At chain length one the space consists of the actual physical eigenvectors in the base space. -/
theorem mem_singularHillRootSpace_one (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (z : ℂ) (x : FourierLebesgueSpace (2:ℝ) (-1) 2) :
    x ∈ singularHillRootSpace q z 1 ↔
      ∃ f : FourierLebesgueSpace (2:ℝ) 1 2, singularHillDomainInclusion f = x ∧
        singularHillOperator q f = z • singularHillDomainInclusion f := by
  rw [mem_singularHillRootSpace_succ q z 0 x]
  change (∃ f : FourierLebesgueSpace (2:ℝ) 1 2, singularHillDomainInclusion f = x ∧
    singularHillOperator q f-z • singularHillDomainInclusion f = 0) ↔ _
  simp only [sub_eq_zero]

/-- Every actual generalized eigenvector has an H1 representative and an H1 right-hand side. -/
theorem exists_H1_chain_rhs_of_mem_singularHillRootSpaceTop
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ)
    (x : FourierLebesgueSpace (2:ℝ) (-1) 2) (hx : x ∈ singularHillRootSpaceTop q z) :
    ∃ f g : FourierLebesgueSpace (2:ℝ) 1 2, singularHillDomainInclusion f = x ∧
      singularHillOperator q f-z • singularHillDomainInclusion f = singularHillDomainInclusion g := by
  obtain ⟨n,hn⟩ := (mem_singularHillRootSpaceTop q z x).mp hx
  cases n with
  | zero =>
    have hx0 : x = 0 := hn
    exact ⟨0,0,by simp [hx0],by simp⟩
  | succ n =>
    obtain ⟨f,hf,hprev⟩ := (mem_singularHillRootSpace_succ q z n x).mp hn
    obtain ⟨g,hg⟩ := singularHillRootSpaceTop_le_domain q z
      ((mem_singularHillRootSpaceTop q z _).mpr ⟨n,hprev⟩)
    exact ⟨f,g,hf,hg.symm⟩

end NLS.KdV
