import NLS.SequenceSpaces.PeriodOneSobolevMiuraInverse

/-! # Stronger Sobolev analyticity of the SAME actual rough Miura branch

The actual rough branch is identified with native Sobolev inverse germs
by the proved weak local uniqueness. No independent choice of a lift is
substituted for the given branch.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS

/-- An actual weak lift of a native H^(t-1) datum has the SAME literal
coefficients as a native H^t lift solving the actual stronger equation. -/
theorem exists_periodOneSobolevMiura_lift_of_rough_solution
    (m : ℕ) (t : ℝ) (ht : 0≤t)
    (q : WeightedCoeff (Weight.sobolev (t-1)) 2) (v : Coeff 2)
    (hv : periodOneShiftedMiura m v=periodOneSobolevImageInclusion t ht q) :
    ∃ a : WeightedCoeff (Weight.sobolev t) 2,
      WeightedCoeff.sobolevToL2 ht a=v ∧ periodOneSobolevShiftedMiura m t ht a=q := by
  have hf : Memℓp (fun n => (Weight.sobolev (t-1) n : ℂ)*
      (periodOneSobolevImageInclusion t ht q).val n) 2 := by
    simpa only [periodOneSobolevImageInclusion_apply] using
      (show Memℓp (fun n => (Weight.sobolev (t-1) n : ℂ)*q.val n) 2 from q.property)
  have H := periodOneShiftedMiura_lift_mem_sobolev m _ v hv (t-1) (by linarith) hf
  have hmem : Memℓp (fun n => (Weight.sobolev t n : ℂ)*v n) 2 := by
    simpa only [sub_add_cancel] using H
  let a : WeightedCoeff (Weight.sobolev t) 2 := ⟨v,hmem⟩
  have ha : WeightedCoeff.sobolevToL2 ht a=v := by
    ext n
    exact WeightedCoeff.sobolevToL2_apply ht a n
  refine ⟨a,ha,?_⟩
  apply WeightedCoeff.sobolevInclusion_injective (by linarith : -1≤t-1)
  change periodOneSobolevImageInclusion t ht (periodOneSobolevShiftedMiura m t ht a)=
    periodOneSobolevImageInclusion t ht q
  rw [periodOneSobolevShiftedMiura_inclusion,ha,hv]

/-- A given ACTUAL rough analytic branch has a complex analytic lift into
the stronger native Sobolev space around EVERY eligible source where its
ACTUAL weak Jacobian is bijective. The stronger function agrees EXACTLY
with that SAME rough branch after coefficient inclusion. -/
theorem exists_analytic_strong_periodOneMiura_branch
    (m : ℕ) (t : ℝ) (ht : 0≤t)
    (U : Set PeriodOneHminusOne) (hU : IsOpen U)
    (G : PeriodOneHminusOne → Coeff 2) (hGa : AnalyticOnNhd ℂ G U)
    (hsolve : ∀ p∈U, periodOneShiftedMiura m (G p)=p)
    (q : WeightedCoeff (Weight.sobolev (t-1)) 2)
    (hq : periodOneSobolevImageInclusion t ht q∈U)
    (hb : Function.Bijective (periodOneMiuraJacobian m (G (periodOneSobolevImageInclusion t ht q)))) :
    ∃ V : Set (WeightedCoeff (Weight.sobolev (t-1)) 2), IsOpen V ∧ q∈V ∧
      ∃ g : WeightedCoeff (Weight.sobolev (t-1)) 2 → WeightedCoeff (Weight.sobolev t) 2,
        AnalyticOnNhd ℂ g V ∧ ∀ p∈V,
          periodOneSobolevImageInclusion t ht p∈U ∧
          WeightedCoeff.sobolevToL2 ht (g p)=G (periodOneSobolevImageInclusion t ht p) ∧
          periodOneSobolevShiftedMiura m t ht (g p)=p := by
  let L := periodOneSobolevImageInclusion t ht
  let v := G (L q)
  obtain ⟨a,ha,hM⟩ := exists_periodOneSobolevMiura_lift_of_rough_solution m t ht q v (hsolve _ hq)
  have hbA : Function.Bijective (periodOneMiuraJacobian m (WeightedCoeff.sobolevToL2 ht a)) := by
    rwa [ha]
  obtain ⟨VS,WS,_hVS,hWS,haVS,hqWS,g,hga,hleft,hright⟩ :=
    exists_periodOneSobolevMiura_inverse_at m t ht a hbA
  have hqWS' : q∈WS := by simpa only [hM] using hqWS
  have hgq : g q=a := by simpa only [hM] using hleft a haVS
  obtain ⟨VW,_WW,hVW,_hWW,hvVW,_hqWW,gw,_hgwa,hleftw,_hrightw⟩ :=
    exists_periodOneMiura_inverse_at_of_bijectiveJacobian m v hb
  have hbase : WeightedCoeff.sobolevToL2 ht (g q)=G (L q) := by rw [hgq,ha]
  obtain ⟨V,hV,hqV,hgV,hdata⟩ :=
    NLS.ComplexAnalysis.exists_strong_analytic_branch_of_local_inverses
      (periodOneSobolevShiftedMiura m t ht) (periodOneShiftedMiura m)
      (WeightedCoeff.sobolevToL2 ht) L
      (fun a => (periodOneSobolevShiftedMiura_inclusion m t ht a).symm)
      U hU G hGa.continuousOn hsolve WS hWS g hga
      (fun p hp => (hright p hp).2) VW hVW gw hleftw q hqWS' hq hbase hvVW
  exact ⟨V,hV,hqV,g,hgV,hdata⟩

end NLS
