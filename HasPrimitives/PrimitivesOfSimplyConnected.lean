import HasPrimitives.Basic

open scoped Interval

noncomputable def CurvInt (t₁ t₂ : ℝ) (f : ℂ → ℂ) (γ : ℝ → ℂ) : ℂ :=
   ∫ t in t₁..t₂, deriv γ t • f (γ t)

-- TO DO: move to `Mathlib.Data.Set.Intervals.UnorderedInterval` (Yael add API?)
def Set.uIoo {α : Type*} [LinearOrder α]  : α → α → Set α := fun a b => Set.Ioo (min a b) (max a b)

-- TO DO: move to `Mathlib.Data.Set.Intervals.UnorderedInterval` (Yael add API?)
theorem Set.uIoo_comm {α : Type*} [LinearOrder α] [Lattice α] (a : α) (b : α) : Set.uIoo a b = Set.uIoo b a := sorry

-- TO DO: move to `Mathlib.Data.Set.Intervals.UnorderedInterval` (Yael add API?)
theorem Set.uIoo_of_le {α : Type*} [LinearOrder α] [Lattice α] {a : α} {b : α} (h : a ≤ b) :
    Set.uIoo a b = Set.Ioo a b := sorry

-- an open interval is equal to a closed one up to measure zero
lemma uIoo_eqM_uIcc (a b : ℝ) : Set.uIoo a b =ᵐ[MeasureTheory.volume] Set.uIcc a b := by
  wlog h : a ≤ b
  · convert this b a (by linarith) using 1
    · rw [Set.uIoo_comm]
    · rw [Set.uIcc_comm]
  rw [Set.uIcc_of_le h, Set.uIoo_of_le h]
  refine MeasureTheory.ae_eq_set.mpr ?_
  constructor
  · -- convert volume of empty is zero
    convert MeasureTheory.measure_empty using 2
    refine Set.diff_eq_empty.mpr ?h.e'_2.h.e'_3.a
    exact Set.Ioo_subset_Icc_self
  · rw [Set.Icc_diff_Ioo_same h]
    refine Set.Finite.measure_zero ?right.h MeasureTheory.volume
    exact Set.toFinite {a, b}


-- move near `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`
theorem intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le' {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] [NormedSpace ℝ E] {f : ℝ → E} {f' : ℝ → E} {a : ℝ} {b : ℝ} (hab : a ≤ b) (hcont : ContinuousOn f (Set.Icc a b)) (hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x) (hint : IntervalIntegrable f' MeasureTheory.volume a b) :
∫ (y : ℝ) in a..b, f' y = f b - f a := by sorry


theorem curvInt_eval_of_primitive {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂) {γ : ℝ → ℂ} {f F : ℂ → ℂ} {U : Set ℂ}
    (U_open : IsOpen U) (γ_in_U : ∀ t, t ∈ Set.Icc t₁ t₂ → γ t ∈ U)
    (F_prim : ∀ z ∈ U, HasDerivAt F (f z) z)
    (hγ : DifferentiableOn ℝ γ (Set.Ioo t₁ t₂)) :
    CurvInt t₁ t₂ f γ = F (γ t₂) - F (γ t₁) := by
  have cont₁ : ∀ t ∈ Set.Icc t₁ t₂, ContinuousWithinAt (fun {t₂} => F (γ t₂)) (Set.Icc t₁ t₂) t := sorry
  have cont₂ : ∀ t ∈ [[t₁, t₂]], ContinuousWithinAt (fun y => deriv γ y • f (γ y)) [[t₁, t₂]] t := sorry
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht (f := F ∘ γ)
    (fun t ht' ↦ cont₁ t ht') ?_ (ContinuousOn.intervalIntegrable (fun t ht' ↦ cont₂ t ht'))
  intro t ht'
  convert HasDerivAt.comp (h₂ := F) (h := γ) (x := t) (h₂' := f (γ t)) (h' := deriv γ t) (F_prim (γ t)
    (γ_in_U t (Set.mem_Icc_of_Ioo ht'))) ?_ using 1
  · simp only [smul_eq_mul]
    ring
  · rw [hasDerivAt_deriv_iff]
    exact (hγ t ht').differentiableAt
      (mem_nhds_iff.mpr ⟨Set.Ioo t₁ t₂, Eq.subset rfl, isOpen_Ioo, ht'⟩)

/-- Two curves are `Homotopic` in `U` if there exists a homotopy through differentiable curves -/
def Homotopic (t₁ t₂ : ℝ) (γ₀ γ₁ : ℝ → ℂ) (U : Set ℂ) : Prop := ∃ (γ : ℝ × ℝ → ℂ),
    (γ '' (Set.Icc 0 1 ×ˢ [[t₁, t₂]]) ⊆ U) ∧ -- image is contained in U
    (ContinuousOn γ (Set.Icc 0 1 ×ˢ [[t₁, t₂]])) ∧ -- jointly continuous
    (∀ t ∈ [[t₁, t₂]], γ ⟨0, t⟩ = γ₀ t) ∧ (∀ t ∈ [[t₁, t₂]], γ ⟨1, t⟩ = γ₁ t) ∧ -- starts at γ₀ and ends at γ₁
    (∀ s ∈ Set.Icc 0 1, γ ⟨s, t₁⟩ = γ₀ t₁) ∧ (∀ s ∈ Set.Icc 0 1, γ ⟨s, t₂⟩ = γ₁ t₂) -- fixed endpoints

theorem Homotopic.symm (t₁ t₂ : ℝ) (γ₀ γ₁ : ℝ → ℂ) (U : Set ℂ)
    (h : Homotopic t₁ t₂ γ₀ γ₁ U) : Homotopic t₂ t₁ γ₀ γ₁ U := by
  sorry

/-- Two curves are `DifferentiablyHomotopic` in `U` if there exists a homotopy through differentiable curves -/
def DifferentiablyHomotopic (t₁ t₂ : ℝ) (γ₀ γ₁ : ℝ → ℂ) (U : Set ℂ) : Prop := ∃ (γ : ℝ × ℝ → ℂ),
    (γ '' (Set.Icc 0 1 ×ˢ [[t₁, t₂]]) ⊆ U) ∧ -- image is contained in U
    (ContinuousOn γ (Set.Icc 0 1 ×ˢ [[t₁, t₂]])) ∧ -- jointly continuous
    (∀ s ∈ Set.Icc 0 1, DifferentiableOn ℝ γ ({s} ×ˢ (Set.uIoo t₁ t₂))) ∧ -- differentiable in second variable
    (∀ t ∈ [[t₁, t₂]], γ ⟨0, t⟩ = γ₀ t) ∧ (∀ t ∈ [[t₁, t₂]], γ ⟨1, t⟩ = γ₁ t) ∧ -- starts at γ₀ and ends at γ₁
    (∀ s ∈ Set.Icc 0 1, γ ⟨s, t₁⟩ = γ₀ t₁) ∧ (∀ s ∈ Set.Icc 0 1, γ ⟨s, t₂⟩ = γ₁ t₂) -- fixed endpoints


/-- If two curves are `DiffHomotopic`, then the `CurvInt` of a holomorphic function over the two curves is the same. -/
theorem curvInt_eq_of_diffHomotopic {t₁ t₂ : ℝ} {γ₀ γ₁ : ℝ → ℂ} {f : ℂ → ℂ} {U : Set ℂ}
    (hom : DifferentiablyHomotopic t₁ t₂ γ₀ γ₁ U)
    (f_holo : DifferentiableOn ℂ f U) :
    CurvInt t₁ t₂ f γ₀ = CurvInt t₁ t₂ f γ₁ := by
  sorry
#exit
  obtain ⟨γ, hU, hcont, hdiff, h₀, h₁, h₂, h₃⟩ := DifferentiablyHomotopic_of_OpenHomotopic U_open hom
  have icc_is : [[t₁, t₂]] = Set.Icc t₁ t₂ := by simp [ht]
  let K := γ '' (Set.Icc 0 1 ×ˢ [[t₁, t₂]])
  have K_cpt : IsCompact K
  · refine IsCompact.image_of_continuousOn ?hK.hs hcont
    refine IsCompact.prod ?_ (isCompact_uIcc (a := t₁) (b := t₂))
    have := isCompact_uIcc (a := (0:ℝ)) (b := 1)
    rwa [(by simp : [[(0 : ℝ), 1]] = Set.Icc 0 1)] at this
  have : ∃ ε > 0, ∀ z ∈ K, Metric.ball z (3 * ε) ⊆ U := sorry
  obtain ⟨ε, ε_pos, ε_ballWithinU⟩ := this
  have : ∃ δ > 0, ∀ s₁ ∈ Set.Icc 0 1, ∀ s₂ ∈ Set.Icc 0 1, ∀ t ∈ [[t₁, t₂]], |s₁ - s₂| < δ →
    Complex.abs (γ ⟨s₁, t⟩ - γ ⟨s₂, t⟩) < ε := sorry
  obtain ⟨δ, δ_pos, δ_UnifCont⟩ := this


  sorry

#exit

theorem DifferentiablyHomotopic_of_OpenHomotopic {t₁ t₂ : ℝ} {γ₀ γ₁ : ℝ → ℂ} {U : Set ℂ} (U_open : IsOpen U) (γ₀_diffble : DifferentiableOn ℝ γ₀ (Set.Ioo t₁ t₂))
(γ₁_diffble : DifferentiableOn ℝ γ₁ (Set.Ioo t₁ t₂))
    (h : Homotopic t₁ t₂ γ₀ γ₁ U) : DifferentiablyHomotopic t₁ t₂ γ₀ γ₁ U := by
  sorry


theorem curvInt_eq_of_homotopic {t₁ t₂ : ℝ} {γ₀ γ₁ : ℝ → ℂ} {f : ℂ → ℂ} {U : Set ℂ}
    (U_open : IsOpen U) (hom : Homotopic t₁ t₂ γ₀ γ₁ U)
    (f_holo : DifferentiableOn ℂ f U) :


-- main theorem: holomorphic functions on simply connected open sets have primitives
theorem HasPrimitivesOfSimplyConnected (U : Set ℂ) (hSc : SimplyConnectedSpace U) (hO : IsOpen U) :
    HasPrimitives U := by
  sorry
