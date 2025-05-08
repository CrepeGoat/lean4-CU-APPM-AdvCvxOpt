import Init.Prelude
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Topology.Defs.Basic

import CvxOpt._00_IntroToOptProblems


section main
variable
    {n : Nat}
    {D: Type*}
    {R: Type*}

-- @[deprecated "just use `x ∈ C`" (since := "2025-03-27")]
def FeasiblePoint
    (C : Set D)
    (x : D)
    : Prop := x ∈ C

example
    [LE R] {C : Set D} {x : D}
    : FeasiblePoint C x ↔ x ∈ C
    := by rfl

-- @[deprecated "just use `x ∈ ArgumentMinimumOn f C`" (since := "2025-03-27")]
def GlobalMinimizer
    [LE R]
    (f: D → R)
    (C : Set D)
    (x : D)
    : Prop := x ∈ C ∧ ∀ y ∈ C, f x ≤ f y

example
    [LE R] {f: D → R} {C : Set D} {x : D}
    : GlobalMinimizer f C x ↔ x ∈ ArgumentMinimumOn f C
    := by
    simp [GlobalMinimizer, ArgumentMinimumOn, MinimumOn, IsLeast, lowerBounds]
    intro xinC _
    constructor
    case left => exact xinC
    case right => exists x

/- Note: solutions may not exist-/
example
    : ArgumentMinimumOn (fun x : NNReal => x ^ 2) (setOf (fun x => 0 < x ∧ x < 1)) = ∅
    := by
    rw [← Set.not_nonempty_iff_eq_empty]
    simp [ArgumentMinimumOn, MinimumOn, IsLeast, lowerBounds, Set.Nonempty]
    intro x h h'
    exists (x / 2)^2, x / 2
    simp
    constructor
    case left => exact h
    case right =>

    constructor
    case left =>
        simp [div_lt_iff₀]
        apply lt_trans
        exact h'
        simp
    case right =>

    apply pow_lt_pow_left₀
    case a => simp
    case hab => simp [h]
    case ha => simp [h']

def LocalMinimizer
    [TopologicalSpace D] [LE R]
    (f: D → R)
    (C: Set D)
    (x : D)
    : Prop
    := (x ∈ C) ∧ ∃ x_nhd ∈ nhdsWithin x C, ∀ y ∈ x_nhd, f x ≤ f y

theorem global_min_then_local_min
    [TopologicalSpace D] [LE R]
    {f: D → R}
    {C: Set D}
    {x : D}
    : GlobalMinimizer f C x → LocalMinimizer f C x
    := by
    simp [GlobalMinimizer, LocalMinimizer, nndist]
    intro hx hXIsMin
    constructor
    exact hx
    refine Filter.eventually_iff_exists_mem.mp ?_
    exact eventually_nhdsWithin_of_forall hXIsMin

def StrictLocalMinimizer
    [TopologicalSpace D] [LT R]
    (f: D → R)
    (C: Set D)
    (x : D)
    : Prop
    := (x ∈ C) ∧ ∃ x_nhd ∈ nhdsWithin x C, ∀ y ∈ x_nhd, f x < f y

def IsolatedStrictLocalMinimizer
    [TopologicalSpace D] [LT R] [LE R]
    (f: D → R)
    (C: Set D)
    (x : D)
    : Prop
    :=
        StrictLocalMinimizer f C x
        ∧ ∃ x_nhd ∈ nhdsWithin x C, ∀ y ∈ x_nhd, (LocalMinimizer f C y → y = x)

def CriticalPoint
    [RCLike R] [NormedAddCommGroup D] [InnerProductSpace R D] [CompleteSpace D]
    (f: D → R)
    (C : Set D)
    (x : D)
    : Prop
    := HasGradientWithinAt f 0 C x

example
    [InnerProductSpace ℝ (Fin n → ℝ)]
    : CriticalPoint (fun x: Fin n → ℝ => ‖x‖ ^ 2) Set.univ 0
    := by
    unfold CriticalPoint
    refine hasGradientWithinAt_univ.mpr ?_
    refine hasGradientAt_iff_isLittleO_nhds_zero.mpr ?_
    simp
    refine Asymptotics.isLittleO_norm_pow_id ?_
    exact Nat.one_lt_two

theorem local_min_on_open_set_then_critical_point
    [NormedAddCommGroup D] [CompleteSpace D]
    [LE R] [RCLike R]
    [InnerProductSpace R D]
    {f: D → R}
    {C: Set D}
    {x : D}
    (hLocalMin : LocalMinimizer f C x)
    (hCIsOpen : IsOpen C)
    : CriticalPoint f C x
    := by
    sorry
    -- unfold fderiv

    /-
    - take a local min -> it's smaller than all other points in some open ball
    - C is open -> that ball of points are all feasible
    - for each component / dimension of xmin:
        - add ε to xmin_i -> this point is bigger -> the gradient must be non-negative
        - sub ε to xmin_i -> this point is also bigger -> the gradient must be non-positive
        -> the gradient on this component is zero
    - the overall gradient is zero
    -/
    sorry

private def nhd0_contains_neg
    : ∀ nhd0 ∈ nhds (0 : ℝ), ∃ x ∈ nhd0, x < 0
    := by
    intro nhd0 hNhd0
    have hIoo0 := mem_nhds_iff_exists_Ioo_subset.mp hNhd0
    constructor
    case w => exact hIoo0.choose * (1 / 2)

    have _0inIoo := hIoo0.choose_spec.choose_spec.left
    rw [← Set.Ioo_def] at _0inIoo
    simp at _0inIoo
    have hLLt0 := _0inIoo.left

    constructor
    case right => refine mul_neg_of_neg_of_pos hLLt0 one_half_pos

    have hIsSubset := hIoo0.choose_spec.choose_spec.right
    rw [(Set.Ioo hIoo0.choose hIoo0.choose_spec.choose).subset_def] at hIsSubset
    apply hIsSubset
    rw [← Set.Ioo_def]
    constructor

    nth_rewrite 1 [← mul_one hIoo0.choose]
    refine mul_lt_mul_of_neg_left one_half_lt_one hLLt0

    apply lt_of_le_of_lt
    case h.left.a.right.b => exact 0
    case h.left.a.right.hbc => exact _0inIoo.right
    rw [le_iff_lt_or_eq]; apply Or.intro_left
    refine mul_neg_of_neg_of_pos hLLt0 one_half_pos

def SaddlePoint
    [LE R] [RCLike R] [NormedAddCommGroup D] [InnerProductSpace R D] [CompleteSpace D]
    (f: D → R)
    (C : Set D)
    (x : D)
    : Prop
    := CriticalPoint f C x ∧ ¬LocalMinimizer f C x

example
    -- [PreirreducibleSpace ℝ]
    : SaddlePoint (fun x: ℝ => x ^ 3) Set.univ 0
    := by
    simp only [SaddlePoint, CriticalPoint, hasGradientWithinAt_univ, LocalMinimizer, Set.mem_univ,
      nhdsWithin_univ, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, true_and,
      not_exists, not_and, not_forall, Classical.not_imp, not_le]
    constructor
    case left =>
        refine HasDerivAt.hasGradientAt' ?_
        unfold HasDerivAt
        refine hasDerivAtFilter_iff_isLittleO.mpr ?_
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero, smul_eq_mul,
          mul_zero]
        refine Asymptotics.isLittleO_pow_id ?_
        exact Nat.one_lt_succ_succ 1
    case right =>
        intro nhd0 hNhd0
        -- rw [mem_nhds_iff] at hNhd0
        refine bex_def.mpr ?_
        have three_odd : Odd 3 := by
            exact Nat.odd_iff.mpr rfl
        simp_rw [three_odd.pow_neg_iff]
        apply nhd0_contains_neg
        exact hNhd0

theorem inf_on_compact_set_then_min
    [TopologicalSpace D] [LE R]
    {f: D → R}
    {C: Set D}
    {inf : R}
    (hinf : InfimumOn f C inf)
    (hCIsCompact : IsCompact C)
    : MinimumOn f C inf
    := by
    sorry

end main
