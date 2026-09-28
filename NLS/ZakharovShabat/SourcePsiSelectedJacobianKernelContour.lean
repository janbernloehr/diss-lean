import NLS.ZakharovShabat.SourcePsiSelectedJacobianEntry
import NLS.ZakharovShabat.SourcePsiCandidateContourVariation

/-!
# Contour formula for the bounded selected Jacobian

The selected sequence-valued equation agrees locally with its scalar
contour coordinates. This file transfers the scalar derivative formula
to an arbitrary direction of the actual bounded Jacobian, rather than
only to its matrix entries. It is the kernel-to-contour bridge in
Lemma 12.7.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Local coordinate equality identifies every direction of the
bounded selected Jacobian with the corresponding scalar derivative. -/
theorem sourcePsiSelectedRootJacobian_apply_eq_deletedCoordinate_fderiv
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (U : Set (DeletedCoeff p n × CoeffPair p))
    (hUopen : IsOpen U)
    (hcoord : ∀ t ∈ U, ∀ m : ℤ,
      (sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2 : Coeff p) m =
        sourcePsiEquationCoordinate hp hp1 n m
          (t.1 : Coeff p) t.2 (c m) (R m))
    (hdiff : DifferentiableOn ℂ
      (fun t : DeletedCoeff p n × CoeffPair p =>
        sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2) U)
    (a : DeletedCoeff p n) (ψ : CoeffPair p) (hpair : (a,ψ) ∈ U)
    (m : ℤ) (h : DeletedCoeff p n) :
    ((sourcePsiSelectedRootJacobian hp hp1 n c R a ψ h :
      DeletedCoeff p n) : Coeff p) m =
      (fderiv ℂ (fun b : DeletedCoeff p n =>
        sourcePsiDeletedEquationCoordinate hp hp1 n m b ψ
          (c m) (R m)) a) h := by
  let F : DeletedCoeff p n → DeletedCoeff p n :=
    fun b => sourcePsiSelectedEquationSequence hp hp1 n c R b ψ
  let L : DeletedCoeff p n →L[ℂ] ℂ :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p m).comp
      ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.subtypeL)
  let Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n :=
    sourcePsiSelectedRootJacobian hp hp1 n c R a ψ
  have hpairDiff : DifferentiableAt ℂ
      (fun t : DeletedCoeff p n × CoeffPair p =>
        sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2)
      (a,ψ) :=
    (hdiff (a,ψ) hpair).differentiableAt (hUopen.mem_nhds hpair)
  have hinc : DifferentiableAt ℂ
      (fun b : DeletedCoeff p n => (b,ψ)) a := by fun_prop
  have hF : HasFDerivAt F Q a := by
    exact (hpairDiff.comp a hinc).hasFDerivAt
  have hLF : HasFDerivAt (fun b => L (F b)) (L.comp Q) a :=
    L.hasFDerivAt.comp a hF
  have hUevent : ∀ᶠ b : DeletedCoeff p n in 𝓝 a, (b,ψ) ∈ U := by
    exact (continuousAt_id.prodMk continuousAt_const).eventually
      (hUopen.mem_nhds hpair)
  have hEq : (fun b : DeletedCoeff p n => L (F b)) =ᶠ[𝓝 a]
      (fun b : DeletedCoeff p n =>
        sourcePsiDeletedEquationCoordinate hp hp1 n m b ψ
          (c m) (R m)) := by
    filter_upwards [hUevent] with b hb
    exact hcoord (b,ψ) hb m
  have hderiv :
      fderiv ℂ (fun b : DeletedCoeff p n => L (F b)) a =
      fderiv ℂ (fun b : DeletedCoeff p n =>
        sourcePsiDeletedEquationCoordinate hp hp1 n m b ψ
          (c m) (R m)) a := hEq.fderiv_eq
  change (L.comp Q) h =
    (fderiv ℂ (fun b : DeletedCoeff p n =>
      sourcePsiDeletedEquationCoordinate hp hp1 n m b ψ
        (c m) (R m)) a) h
  rw [← hderiv, hLF.fderiv]

/-- On an admissible selected circle, every coordinate of the bounded
Jacobian is the contour integral of the entire numerator variation. -/
theorem sourcePsiSelectedRootJacobian_apply_eq_variation_contour
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (U : Set (DeletedCoeff p n × CoeffPair p))
    (hUopen : IsOpen U)
    (hcoord : ∀ t ∈ U, ∀ m : ℤ,
      (sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2 : Coeff p) m =
        sourcePsiEquationCoordinate hp hp1 n m
          (t.1 : Coeff p) t.2 (c m) (R m))
    (hdiff : DifferentiableOn ℂ
      (fun t : DeletedCoeff p n × CoeffPair p =>
        sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2) U)
    (a : DeletedCoeff p n) (ψ : CoeffPair p) (hpair : (a,ψ) ∈ U)
    (hreal : IsRealType (CoeffPair.toMax p ψ))
    (m : ℤ) (hR : 0 ≤ R m)
    (hcircle : sphere (c m) (R m) ⊆
      sourceCanonicalRootDomain hp hp1 ψ)
    (h : DeletedCoeff p n) :
    ((sourcePsiSelectedRootJacobian hp hp1 n c R a ψ h :
      DeletedCoeff p n) : Coeff p) m =
      ((n-m : ℤ) : ℂ) *
        (∮ z in C(c m,R m),
          sourcePsiCandidateVariation n (a : Coeff p)
            (h : Coeff p) z /
            sourceCanonicalRoot hp hp1 ψ z) := by
  rw [sourcePsiSelectedRootJacobian_apply_eq_deletedCoordinate_fderiv
    hp hp1 n c R U hUopen hcoord hdiff a ψ hpair m h]
  obtain ⟨V,hVopen,hbase,_,hVdiff⟩ :=
    exists_local_sourcePsiEquationCoordinate_differentiableOn
      hp hp1 n m (a : Coeff p) ψ hreal (c m) (R m) hR hcircle
  have hpairDiff : DifferentiableAt ℂ
      (fun t : Coeff p × CoeffPair p =>
        sourcePsiEquationCoordinate hp hp1 n m t.1 t.2 (c m) (R m))
      ((a : Coeff p),ψ) :=
    (hVdiff _ hbase).differentiableAt (hVopen.mem_nhds hbase)
  have hinc : DifferentiableAt ℂ
      (fun b : Coeff p => (b,ψ)) (a : Coeff p) := by fun_prop
  have hambient : DifferentiableAt ℂ
      (fun b : Coeff p =>
        sourcePsiEquationCoordinate hp hp1 n m b ψ (c m) (R m))
      (a : Coeff p) := by
    exact DifferentiableAt.comp
      (f := fun b : Coeff p => (b,ψ))
      (g := fun t : Coeff p × CoeffPair p =>
        sourcePsiEquationCoordinate hp hp1 n m t.1 t.2 (c m) (R m))
      (a : Coeff p) hpairDiff hinc
  let S : DeletedCoeff p n →L[ℂ] Coeff p :=
    ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.subtypeL)
  have hdeleted : HasFDerivAt
      (fun b : DeletedCoeff p n =>
        sourcePsiDeletedEquationCoordinate hp hp1 n m b ψ
          (c m) (R m))
      ((fderiv ℂ (fun b : Coeff p =>
        sourcePsiEquationCoordinate hp hp1 n m b ψ
          (c m) (R m)) (a : Coeff p)).comp S) a := by
    exact HasFDerivAt.comp a hambient.hasFDerivAt S.hasFDerivAt
  obtain ⟨V',_,hbase',hformula⟩ :=
    exists_local_sourcePsiEquationCoordinate_fderiv_root_direction
      hp hp1 n m (a : Coeff p) ψ hreal (c m) (R m) hR hcircle
  rw [hdeleted.fderiv]
  have hS : S h = (h : Coeff p) := rfl
  rw [ContinuousLinearMap.comp_apply, hS]
  exact
    hformula (a : Coeff p) ψ hbase' (h : Coeff p)

/-- A kernel direction makes the variation contour integral vanish in
every retained row. This is the first equation in Lemma 12.7. -/
theorem sourcePsiSelectedRootJacobian_kernel_variation_contour_zero
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (U : Set (DeletedCoeff p n × CoeffPair p))
    (hUopen : IsOpen U)
    (hcoord : ∀ t ∈ U, ∀ m : ℤ,
      (sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2 : Coeff p) m =
        sourcePsiEquationCoordinate hp hp1 n m
          (t.1 : Coeff p) t.2 (c m) (R m))
    (hdiff : DifferentiableOn ℂ
      (fun t : DeletedCoeff p n × CoeffPair p =>
        sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2) U)
    (a : DeletedCoeff p n) (ψ : CoeffPair p) (hpair : (a,ψ) ∈ U)
    (hreal : IsRealType (CoeffPair.toMax p ψ))
    (m : ℤ) (hmn : m ≠ n) (hR : 0 ≤ R m)
    (hcircle : sphere (c m) (R m) ⊆
      sourceCanonicalRootDomain hp hp1 ψ)
    (h : DeletedCoeff p n)
    (hkernel : sourcePsiSelectedRootJacobian hp hp1 n c R a ψ h = 0) :
    (∮ z in C(c m,R m),
      sourcePsiCandidateVariation n (a : Coeff p)
        (h : Coeff p) z /
        sourceCanonicalRoot hp hp1 ψ z) = 0 := by
  have hformula := sourcePsiSelectedRootJacobian_apply_eq_variation_contour
    hp hp1 n c R U hUopen hcoord hdiff a ψ hpair hreal m hR hcircle h
  rw [hkernel] at hformula
  have hweight : ((n-m : ℤ) : ℂ) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr (Ne.symm hmn)
  have hproduct : ((n-m : ℤ) : ℂ) *
      (∮ z in C(c m,R m),
        sourcePsiCandidateVariation n (a : Coeff p)
          (h : Coeff p) z /
          sourceCanonicalRoot hp hp1 ψ z) = 0 := by
    simpa using hformula.symm
  exact (mul_eq_zero.mp hproduct).resolve_left hweight

end NLS.ZakharovShabat
