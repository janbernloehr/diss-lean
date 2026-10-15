import NLS.ZakharovShabat.SourceLemma12_10
import NLS.ZakharovShabat.SourcePsiOriginalFiniteGeometry

/-!
# Diagonal normalization on the unchanged original complex domain

The original equation makes every retained period zero. Nested circles in
an existing original family reduce each sufficiently large outer contour
to the omitted period. The exterior limit then gives its value one, or
2π before normalization. Original circle homotopies and winding comparison
transfer this value to every admissible original circuit. The argument
uses no prepackaged diagonal-period field from Theorem 12.1.
-/

noncomputable section
open Set Complex Filter Topology Metric NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
variable {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Retained periods vanish directly from the actual original equation. -/
theorem SourceLemma12_10Data.original_retained_contour_zero
    (H : SourceLemma12_10Data hp hp1 W₀ W s) (hW₀ : IsOpen W₀)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n m : ℤ) (hm : m ≠ n)
    (D : SourceCriticalRootPeriodCircle hp hp1 ψ m) :
    sourcePsiContour hp hp1 n (s n ψ:Coeff p) ψ (D.center:ℂ) D.radius = 0 := by
  have h := H.psi.previous.quotients.originalEquation_apply hW₀ ψ (H.subset hψ) n (s n ψ) m D
  rw [H.equation ψ hψ n] at h
  have hF : sourcePsiEquationCoordinate hp hp1 n m (s n ψ:Coeff p) ψ (D.center:ℂ) D.radius = 0 := by
    simpa using h.symm
  have hfactor : ((n-m:ℤ):ℂ)*(2*Real.pi:ℂ) ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast sub_ne_zero.mpr hm.symm
    · exact mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  exact (mul_eq_zero.mp hF).resolve_left hfactor


/-- The actual outer period equals any original omitted period at every large cutoff. -/
theorem SourceLemma12_10Data.eventually_original_outer_eq
    (H : SourceLemma12_10Data hp hp1 W₀ W s) (hW₀ : IsOpen W₀)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ)
    (P : SourceCriticalRootPeriodCircle hp hp1 ψ n) :
    ∀ᶠ k : ℕ in atTop,
      sourcePsiContour hp hp1 n (s n ψ:Coeff p) ψ 0 (centralCircleRadius k) =
        sourcePsiContour hp hp1 n (s n ψ:Coeff p) ψ (P.center:ℂ) P.radius := by
  obtain ⟨V,_,_,hψV,_,D,c,hD⟩ := H.psi.previous.quotients.neighborhoods ψ (H.subset hψ)
  obtain ⟨C⟩ := hD.toSourceIsolatingNeighborhoods.nonempty_originalCircleFamily ψ hψV
  filter_upwards [C.eventually_finite_geometry,eventually_ge_atTop n.natAbs] with k hG hk
  have hn : n ∈ Finset.Icc (-(k:ℤ)) (k:ℤ) := by simp only [Finset.mem_Icc]; omega
  exact (hG.eq_omitted_of_retained_zero n hn (s n ψ:Coeff p)
    (fun m _ hmn => H.original_retained_contour_zero hW₀ ψ hψ n m hmn (C.circle m))).trans
      ((C.circle n).psiContour_eq P n (s n ψ:Coeff p))

/-- The actual exterior limit and original contour decomposition give diagonal period one. -/
theorem SourceLemma12_10Data.original_diagonal_contour_one
    (H : SourceLemma12_10Data hp hp1 W₀ W s) (hW₀ : IsOpen W₀)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ)
    (P : SourceCriticalRootPeriodCircle hp hp1 ψ n) :
    sourcePsiContour hp hp1 n (s n ψ:Coeff p) ψ (P.center:ℂ) P.radius = 1 := by
  have hlim := (tendsto_centralCircle_sourcePsiContour hp hp1 n (s n ψ:Coeff p) ψ).congr'
    (H.eventually_original_outer_eq hW₀ ψ hψ n P)
  exact tendsto_nhds_unique tendsto_const_nhds hlim

/-- The unnormalized original diagonal circle period is exactly positive 2π. -/
theorem SourceLemma12_10Data.original_diagonal_raw_circle
    (H : SourceLemma12_10Data hp hp1 W₀ W s) (hW₀ : IsOpen W₀)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ)
    (P : SourceCriticalRootPeriodCircle hp hp1 ψ n) :
    (∮ z in C((P.center:ℂ),P.radius),
      sourcePsiContourIntegrandJoint hp hp1 n (z,((s n ψ:Coeff p),ψ))) = (2*Real.pi:ℂ) := by
  have h := H.original_diagonal_contour_one hW₀ ψ hψ n P
  unfold sourcePsiContour at h
  have hπ : (2*Real.pi:ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  simpa only [← mul_assoc,mul_inv_cancel₀ hπ,one_mul,mul_one] using
    congrArg (fun z : ℂ => (2*Real.pi:ℂ)*z) h

/-- Original circuits have raw period 2π times their winding, on the unchanged W. -/
theorem SourceLemma12_10Data.original_diagonal_raw_circuit_winding
    (H : SourceLemma12_10Data hp hp1 W₀ W s) (hW₀ : IsOpen W₀)
    {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (hψV : ψ ∈ V) (n : ℤ)
    (Γ : PiecewiseC1Loop) (hΓ : Γ.Inside (D n \ sourcePeriodicSegment hp hp1 ψ n)) :
    Γ.integral (fun z => sourcePsiCandidate n (z,(s n ψ:Coeff p))/sourceCanonicalRoot hp hp1 ψ z) =
      (2*Real.pi:ℂ)*Γ.windingIntegral (sourceStandardRootMidpoint hp hp1 ψ n) := by
  obtain ⟨a,r,hr,he⟩ := hD.discs n
  let P := hD.periodCircle ψ hψV n a r hr he
  have h := P.psiCircuit_eq_mul_winding n (s n ψ:Coeff p) Γ (by
    change Γ.Inside (ball (a:ℂ) r \ sourcePeriodicSegment hp hp1 ψ n)
    rwa [← he])
  rw [H.original_diagonal_contour_one hW₀ ψ hψ n P,one_mul] at h
  unfold sourcePsiCircuit at h
  have hπ : (2*Real.pi:ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  simpa only [← mul_assoc,mul_inv_cancel₀ hπ,one_mul] using
    congrArg (fun z : ℂ => (2*Real.pi:ℂ)*z) h

/-- The source's positively winding original cycle has raw integral 2π. -/
theorem SourceLemma12_10Data.original_diagonal_raw_circuit
    (H : SourceLemma12_10Data hp hp1 W₀ W s) (hW₀ : IsOpen W₀)
    {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (hψV : ψ ∈ V) (n : ℤ)
    (Γ : PiecewiseC1Loop) (hΓ : Γ.Inside (D n \ sourcePeriodicSegment hp hp1 ψ n))
    (hw : Γ.windingIntegral (sourceStandardRootMidpoint hp hp1 ψ n) = 1) :
    Γ.integral (fun z => sourcePsiCandidate n (z,(s n ψ:Coeff p))/sourceCanonicalRoot hp hp1 ψ z) =
      (2*Real.pi:ℂ) := by
  rw [H.original_diagonal_raw_circuit_winding hW₀ hD ψ hψ hψV n Γ hΓ,hw,mul_one]

/-- Admissible original period circles exist at every complex source in W. -/
theorem SourceLemma12_10Data.exists_original_diagonal_raw_circle
    (H : SourceLemma12_10Data hp hp1 W₀ W s) (hW₀ : IsOpen W₀)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ) :
    ∃ D : SourceCriticalRootPeriodCircle hp hp1 ψ n,
      (∮ z in C((D.center:ℂ),D.radius),
        sourcePsiContourIntegrandJoint hp hp1 n (z,((s n ψ:Coeff p),ψ))) = (2*Real.pi:ℂ) := by
  obtain ⟨V,_,_,hψV,_,D,c,hD⟩ := H.psi.previous.quotients.neighborhoods ψ (H.subset hψ)
  obtain ⟨a,r,hr,he⟩ := hD.discs n
  let P := hD.toSourceIsolatingNeighborhoods.periodCircle ψ hψV n a r hr he
  exact ⟨P,H.original_diagonal_raw_circle hW₀ ψ hψ n P⟩

/-- The source's large-circle equality holds literally for unnormalized integrals. -/
theorem SourceLemma12_10Data.eventually_original_raw_outer_eq
    (H : SourceLemma12_10Data hp hp1 W₀ W s) (hW₀ : IsOpen W₀)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ)
    (P : SourceCriticalRootPeriodCircle hp hp1 ψ n) :
    ∀ᶠ k : ℕ in atTop,
      (∮ z in C(0,centralCircleRadius k),
        sourcePsiContourIntegrandJoint hp hp1 n (z,((s n ψ:Coeff p),ψ))) =
      (∮ z in C((P.center:ℂ),P.radius),
        sourcePsiContourIntegrandJoint hp hp1 n (z,((s n ψ:Coeff p),ψ))) := by
  have hπ : (2*Real.pi:ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  filter_upwards [H.eventually_original_outer_eq hW₀ ψ hψ n P] with k hk
  exact mul_left_cancel₀ (inv_ne_zero hπ) hk

end NLS.ZakharovShabat
