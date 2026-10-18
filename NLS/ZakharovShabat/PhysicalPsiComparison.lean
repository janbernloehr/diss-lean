import NLS.ZakharovShabat.PhysicalSpectralCircles
import NLS.ZakharovShabat.SourcePsiGapRootMap
import NLS.ZakharovShabat.SourceTheorem12_1

/-! # Physical normalized-function comparison

Gap placement and literal periods are specified using physical spectral
labels and the intrinsic product root. These conditions determine the
deleted l2 root vector and identify it with the source gap solution.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat

/-- Specify deleted l2 roots by physical gap placement and vanishing literal off-diagonal periods. -/
structure PhysicalPsiGapData (n : ℤ) (u : physicalRealSubmodule) (a : DeletedCoeff 2 n) : Prop where
  gap : ∀ m : ℤ, m ≠ n → displacedRoots (a : Coeff 2) m ∈ physicalPeriodicSegment u.val m
  periods : ∀ m : ℤ, m ≠ n → ∀ C : PhysicalSpectralCircle u.val m,
    (∮ z in C((C.center:ℂ),C.radius),
      (-2*jointDeletedSingleSpectralProduct n (z,(a : Coeff 2)))/physicalCanonicalProductRoot u.val z) = 0

/-- The intrinsic physical conditions supply a solution of the established source gap equation. -/
theorem PhysicalPsiGapData.toSource {n : ℤ} {u : physicalRealSubmodule} {a : DeletedCoeff 2 n}
    (h : PhysicalPsiGapData n u a) :
    SourcePsiGapSolution (by simp) (by norm_num) n (sourcePhysicalL2Equiv.symm u.val) a := by
  let φ := sourcePhysicalL2Equiv.symm u.val
  let C (m : ℤ) : PhysicalSpectralCircle u.val m := Classical.choice (exists_physicalSpectralCircle u m)
  let c (m : ℤ) : ℂ := (C m).center
  let R (m : ℤ) : ℝ := (C m).radius
  have he (z : ℂ) : sourcePsiContourIntegrandJoint (by simp) (by norm_num) n (z,((a:Coeff 2),φ)) =
      (-2*jointDeletedSingleSpectralProduct n (z,(a : Coeff 2)))/physicalCanonicalProductRoot u.val z := by
    rw [physicalCanonicalProductRoot_eq]
    rfl
  have hz (m : ℤ) : sourcePsiEquationCoordinate (by simp) (by norm_num) n m (a:Coeff 2) φ (c m) (R m) = 0 := by
    rw [sourcePsiEquationCoordinate_eq_raw_circleIntegral]
    simp_rw [he]
    by_cases hmn : m = n
    · subst m
      simp
    · rw [h.periods m hmn (C m),mul_zero]
  have hcoord (m : ℤ) :
      (sourcePsiSelectedEquationSequence (by simp) (by norm_num) n c R a φ : Coeff 2) m =
        sourcePsiEquationCoordinate (by simp) (by norm_num) n m (a:Coeff 2) φ (c m) (R m) := by
    apply sourcePsiSelectedEquationSequence_apply_of_exists
    exact ⟨0,fun j => by change (0:ℂ) = _; exact (hz j).symm⟩
  refine ⟨?_,c,R,(fun _ => rfl),?_,hcoord,?_⟩
  · intro m hm
    simpa only [physicalPeriodicSegment_eq_source] using h.gap m hm
  · intro m
    exact ⟨(C m).radius_pos,(C m).toSource.gap,(C m).toSource.closedBall_subset_omittedDomain⟩
  · apply Subtype.ext
    ext m
    rw [hcoord,hz]
    rfl

/-- Every physical solution is the unique canonical source gap root vector. -/
theorem PhysicalPsiGapData.eq_sourcePsiGapRoot {n : ℤ} {u : physicalRealSubmodule} {a : DeletedCoeff 2 n}
    (h : PhysicalPsiGapData n u a) :
    a = sourcePsiGapRoot (by simp) (by norm_num) n ⟨sourcePhysicalL2Equiv.symm u.val,u.property⟩ := by
  let φ : realTypeSourceLocus 2 := ⟨sourcePhysicalL2Equiv.symm u.val,u.property⟩
  exact SourcePsiGapSolution.eq_sourcePsiGapRoot (by simp) (by norm_num) n φ a h.toSource

/-- Physical placement and vanishing periods determine the full deleted root vector. -/
theorem PhysicalPsiGapData.unique {n : ℤ} {u : physicalRealSubmodule} {a b : DeletedCoeff 2 n}
    (h : PhysicalPsiGapData n u a) (h' : PhysicalPsiGapData n u b) : a = b :=
  h.eq_sourcePsiGapRoot.trans h'.eq_sourcePsiGapRoot.symm

/-- The canonical source roots have the exact literal physical Kronecker periods. -/
theorem physicalPsi_source_raw_period (n m : ℤ) (u : physicalRealSubmodule)
    (C : PhysicalSpectralCircle u.val m) :
    (∮ z in C((C.center:ℂ),C.radius),
      (-2*jointDeletedSingleSpectralProduct n (z,(sourcePsiGapRoot (by simp) (by norm_num) n
        ⟨sourcePhysicalL2Equiv.symm u.val,u.property⟩ : Coeff 2)))/physicalCanonicalProductRoot u.val z) =
      (2*Real.pi:ℂ)*(if m = n then 1 else 0) := by
  let φ : realTypeSourceLocus 2 := ⟨sourcePhysicalL2Equiv.symm u.val,u.property⟩
  obtain ⟨W₀,_,_,_,W,_,_,hR,s,H⟩ := sourceTheorem12_1 (p := 2) (by simp) (by norm_num)
  have hperiod := H.period φ.val (hR φ.property) n m C.toSource
  rw [H.real_agreement n φ] at hperiod
  have he (z : ℂ) : sourcePsiContourIntegrandJoint (by simp) (by norm_num) n
      (z,((sourcePsiGapRoot (by simp) (by norm_num) n φ:Coeff 2),φ.val)) =
        (-2*jointDeletedSingleSpectralProduct n
          (z,(sourcePsiGapRoot (by simp) (by norm_num) n φ:Coeff 2)))/physicalCanonicalProductRoot u.val z := by
    rw [physicalCanonicalProductRoot_eq]
    rfl
  simp only [sourcePsiContour,PhysicalSpectralCircle.toSource] at hperiod
  simp_rw [he] at hperiod
  have hπ : (2*Real.pi:ℂ) ≠ 0 := mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  have h := congrArg (fun w : ℂ => (2*Real.pi:ℂ)*w) hperiod
  simpa only [← mul_assoc,mul_inv_cancel₀ hπ,one_mul] using h

/-- Physical gap placement and vanishing periods are satisfied at every real input. -/
theorem physicalPsiGapData_source (n : ℤ) (u : physicalRealSubmodule) :
    PhysicalPsiGapData n u (sourcePsiGapRoot (by simp) (by norm_num) n
      ⟨sourcePhysicalL2Equiv.symm u.val,u.property⟩) := by
  let φ : realTypeSourceLocus 2 := ⟨sourcePhysicalL2Equiv.symm u.val,u.property⟩
  constructor
  · intro m hm
    rw [physicalPeriodicSegment_eq_source]
    exact sourcePsiGapRoot_mem_periodicSegment (by simp) (by norm_num) n m hm φ
  · intro m hm C
    simpa only [if_neg hm,mul_zero] using physicalPsi_source_raw_period n m u C

/-- Every real physical source admits exactly one deleted l2 vector with these periods and placement. -/
theorem existsUnique_physicalPsiGapData (n : ℤ) (u : physicalRealSubmodule) :
    ∃! a : DeletedCoeff 2 n, PhysicalPsiGapData n u a :=
  ⟨_,physicalPsiGapData_source n u,fun _ h => h.eq_sourcePsiGapRoot⟩

/-- Choose the roots by the physical placement and period specification. -/
def physicalPsiGapRoot (n : ℤ) (u : physicalRealSubmodule) : DeletedCoeff 2 n :=
  (existsUnique_physicalPsiGapData n u).choose

/-- The selected roots satisfy the intrinsic physical conditions. -/
theorem physicalPsiGapRoot_spec (n : ℤ) (u : physicalRealSubmodule) :
    PhysicalPsiGapData n u (physicalPsiGapRoot n u) :=
  (existsUnique_physicalPsiGapData n u).choose_spec.1

/-- Independent physical selection equals the canonical source root vector. -/
theorem physicalPsiGapRoot_eq_source (n : ℤ) (u : physicalRealSubmodule) :
    physicalPsiGapRoot n u = sourcePsiGapRoot (by simp) (by norm_num) n
      ⟨sourcePhysicalL2Equiv.symm u.val,u.property⟩ :=
  (physicalPsiGapRoot_spec n u).eq_sourcePsiGapRoot

/-- The full physical psi numerator uses the fixed normalized deleted entire product. -/
def physicalPsiFunction (n : ℤ) (u : physicalRealSubmodule) (z : ℂ) : ℂ :=
  -2*jointDeletedSingleSpectralProduct n (z,(physicalPsiGapRoot n u : Coeff 2))

/-- The physical numerator is entire in the spectral parameter. -/
theorem differentiable_physicalPsiFunction (n : ℤ) (u : physicalRealSubmodule) :
    Differentiable ℂ (physicalPsiFunction n u) :=
  differentiable_sourcePsiCandidate (by simp) (by norm_num) n (physicalPsiGapRoot n u : Coeff 2)

/-- Exact normalization on every physical isolating circle, including the diagonal period. -/
theorem physicalPsiFunction_period (n m : ℤ) (u : physicalRealSubmodule)
    (C : PhysicalSpectralCircle u.val m) :
    (2*Real.pi:ℂ)⁻¹*(∮ z in C((C.center:ℂ),C.radius),
      physicalPsiFunction n u z/physicalCanonicalProductRoot u.val z) = if m = n then 1 else 0 := by
  simp only [physicalPsiFunction,physicalPsiGapRoot_eq_source]
  rw [physicalPsi_source_raw_period]
  have hπ : (2*Real.pi:ℂ) ≠ 0 := mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  rw [← mul_assoc,inv_mul_cancel₀ hπ,one_mul]

end NLS.ZakharovShabat
