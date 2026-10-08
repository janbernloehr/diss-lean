import NLS.ZakharovShabat.SourceRealGapFactorBound
import NLS.ZakharovShabat.SourceRealActionBallOverlap

/-! # Uniform continuity on one moving gap near a real source -/
noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The deleted factor evaluated at the signed parameter of a complex gap segment. -/
def sourceGapFactorValue (n : ℤ) (ψ : CoeffPair 2) (t : ℝ) : ℂ :=
  I*sourceCriticalRootRatioExtension (by simp) (by norm_num) n ψ
    (sourceCanonicalRootGapPoint (by simp) (by norm_num) ψ n t)

/-- Joint continuity includes endpoints and collapsed gaps, in the original source topology. -/
theorem continuousAt_sourceGapFactorValue (φ : CoeffPair 2)
    (hφ : IsRealType (CoeffPair.toMax 2 φ)) (n : ℤ) (t : ℝ) (ht : t ∈ Icc (-1:ℝ) 1) :
    ContinuousAt (fun x : ℝ × CoeffPair 2 => sourceGapFactorValue n x.2 x.1) (t,φ) := by
  obtain ⟨W,_,_,hreal,hdata⟩ := exists_global_source_analytic_singleRootQuotient
    (by simp : (2:ℝ≥0∞) ≠ ⊤) (by norm_num)
  obtain ⟨V,_,_,hrealV,hpoint⟩ := exists_global_source_gapPoint_mem_omittedDomain
    (by simp : (2:ℝ≥0∞) ≠ ⊤) (by norm_num)
  let a := sourceCriticalDisplacement (by simp) (by norm_num) φ
  let z := sourceCanonicalRootGapPoint (by simp) (by norm_num) φ n t
  have hQ := ((hdata n).2 (z,(a,φ)) ⟨hreal hφ,hpoint φ (hrealV hφ) n t ht.1 ht.2⟩).continuousAt
  have hL := continuousAt_canonicalPeriodicLeft_periodOne_of_realType (by simp) (by norm_num) φ hφ n
  have hR := continuousAt_canonicalPeriodicRight_periodOne_of_realType (by simp) (by norm_num) φ hφ n
  have hτ : ContinuousAt (fun ψ : CoeffPair 2 => sourceStandardRootMidpoint (by simp) (by norm_num) ψ n) φ :=
    (hL.add hR).div_const 2
  have hδ : ContinuousAt (fun ψ : CoeffPair 2 => sourceStandardRootHalfGap (by simp) (by norm_num) ψ n) φ :=
    (hR.sub hL).div_const 2
  have hτx : ContinuousAt (fun x : ℝ × CoeffPair 2 =>
      sourceStandardRootMidpoint (by simp) (by norm_num) x.2 n) (t,φ) :=
    hτ.comp (x := (t,φ)) (f := fun x : ℝ × CoeffPair 2 => x.2) continuousAt_snd
  have hδx : ContinuousAt (fun x : ℝ × CoeffPair 2 =>
      sourceStandardRootHalfGap (by simp) (by norm_num) x.2 n) (t,φ) :=
    hδ.comp (x := (t,φ)) (f := fun x : ℝ × CoeffPair 2 => x.2) continuousAt_snd
  have htx : ContinuousAt (fun x : ℝ × CoeffPair 2 => (x.1:ℂ)) (t,φ) :=
    Complex.continuous_ofReal.continuousAt.comp (x := (t,φ))
      (f := fun x : ℝ × CoeffPair 2 => x.1) continuousAt_fst
  have hz : ContinuousAt (fun x : ℝ × CoeffPair 2 =>
      sourceCanonicalRootGapPoint (by simp) (by norm_num) x.2 n x.1) (t,φ) := by
    exact hτx.add (hδx.mul htx)
  have ha := (continuousAt_sourceCriticalDisplacement_of_realType (by simp) (by norm_num) φ hφ).comp
    (continuousAt_snd : ContinuousAt (fun x : ℝ × CoeffPair 2 => x.2) (t,φ))
  have h := hQ.comp (x := (t,φ)) (f := fun x : ℝ × CoeffPair 2 =>
    (sourceCanonicalRootGapPoint (by simp) (by norm_num) x.2 n x.1,
      (sourceCriticalDisplacement (by simp) (by norm_num) x.2,x.2)))
    (hz.prodMk (ha.prodMk continuousAt_snd))
  have he : (fun x : ℝ × CoeffPair 2 => sourceGapFactorValue n x.2 x.1) =
      (fun x : ℝ × CoeffPair 2 => sourceSingleRootQuotientJointProduct (by simp) (by norm_num) n
        (sourceCanonicalRootGapPoint (by simp) (by norm_num) x.2 n x.1,
          (sourceCriticalDisplacement (by simp) (by norm_num) x.2,x.2))) := by
    funext x
    simp [sourceGapFactorValue,sourceCriticalRootRatioExtension,sourceCriticalDisplacement,← mul_assoc]
  rw [he]
  exact h

/-- Compactness of the parameter interval turns joint continuity into a uniform
comparison with the real-type projection along the entire moving gap. -/
theorem exists_local_sourceGapFactor_realPart_comparison (φ : CoeffPair 2)
    (hφ : IsRealType (CoeffPair.toMax 2 φ)) (n : ℤ) :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ φ ∈ U ∧ ∀ ψ ∈ U, ∀ t ∈ Icc (-1:ℝ) 1,
      ‖sourceGapFactorValue n ψ t-sourceGapFactorValue n (sourceRealPart ψ) t‖ ≤ 1 := by
  let f : ℝ × CoeffPair 2 → ℝ := fun x =>
    ‖sourceGapFactorValue n x.2 x.1-sourceGapFactorValue n (sourceRealPart x.2) x.1‖
  let D := interior {x : ℝ × CoeffPair 2 | f x < 1}
  have hfix := sourceRealPart_eq_self_of_realType φ hφ
  have hslice : Icc (-1:ℝ) 1 ×ˢ ({φ} : Set (CoeffPair 2)) ⊆ D := by
    rintro ⟨t,ψ⟩ ⟨ht,hψ⟩
    have he : ψ = φ := hψ
    subst ψ
    have hc := continuousAt_sourceGapFactorValue φ hφ n t ht
    have hproj : ContinuousAt (fun x : ℝ × CoeffPair 2 => (x.1,sourceRealPart x.2)) (t,φ) :=
      continuousAt_fst.prodMk ((continuous_sourceRealPart (by simp)).continuousAt.comp continuousAt_snd)
    have hcR : ContinuousAt (fun x : ℝ × CoeffPair 2 => sourceGapFactorValue n x.2 x.1)
        (t,sourceRealPart φ) := by simpa only [hfix] using hc
    have hcR' : ContinuousAt (fun x : ℝ × CoeffPair 2 => sourceGapFactorValue n (sourceRealPart x.2) x.1)
        (t,φ) := hcR.comp (x := (t,φ))
          (f := fun x : ℝ × CoeffPair 2 => (x.1,sourceRealPart x.2)) hproj
    have hd : ContinuousAt f (t,φ) := (hc.sub hcR').norm
    apply mem_interior_iff_mem_nhds.mpr
    exact hd.eventually (gt_mem_nhds (by simp only [f,hfix,sub_self,norm_zero]; norm_num))
  obtain ⟨A,U,_,hU,hKA,hφU,hAU⟩ := generalized_tube_lemma isCompact_Icc isCompact_singleton
    isOpen_interior hslice
  refine ⟨U,hU,hφU (mem_singleton φ),?_⟩
  intro ψ hψ t ht
  have hh : (t,ψ) ∈ {x : ℝ × CoeffPair 2 | f x < 1} :=
    (interior_subset : D ⊆ {x : ℝ × CoeffPair 2 | f x < 1}) (hAU ⟨hKA ht,hψ⟩)
  exact hh.le

end NLS.ZakharovShabat
