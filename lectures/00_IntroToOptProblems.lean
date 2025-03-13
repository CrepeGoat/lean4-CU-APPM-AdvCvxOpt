import Mathlib.Order.Bounds.Basic
import Mathlib.Algebra.Order.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Init.Prelude
import Mathlib.Data.Matrix.Defs
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Data.PNat.Notation
import Mathlib.Data.Real.ConjExponents
import Mathlib.Algebra.Group.Defs



import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
-- import Mathlib.LinearAlgebra.Eigenspace.Minpoly
-- import Mathlib.LinearAlgebra.Charpoly.Basic
-- import Mathlib.Data.Complex.FiniteDimensional

-- import Mathlib.Tactic
-- import Mathlib.Util.Delaborators

-- set_option warningAsError false

-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Order/Group/Defs.html#neg_le_neg

/-!

Math implementation for lecture 00:
https://github.com/stephenbeckr/convex-optimization-class/blob/main/Notes/00_IntroToOptProblems.pdf

uses CvxLean as a reference:
- https://github.com/verified-optimization/CvxLean/blob/c62c2f292c6420f31a12e738ebebdfed50f6f840/CvxLean/Lib/Minimization.lean

-/


/-- min of f(x) for all x in C -/
structure MinimumOn
    {Domain: Type*}
    {Range: Type*} [Preorder Range]
    (objective: Domain → Range)
    (ConstraintSet: Set Domain)
    where
    value : Range
    yIsInImage : ∃ x ∈ ConstraintSet, objective x = value
    isMin: ∀ x ∈ ConstraintSet, value ≤ objective x

/-- max of f(x) for all x in C -/
structure MaximumOn
    {Domain: Type*}
    {Range: Type*} [Preorder Range]
    (objective: Domain → Range)
    (ConstraintSet: Set Domain)
    where
    value : Range
    yIsInImage : ∃ x ∈ ConstraintSet, objective x = value
    isMax: ∀ x ∈ ConstraintSet, objective x ≤ value

/- Remark -/
/-- min_x f(x) = -max_x (-f(x)) -/
def min_obj_to_neg_max_neg_obj
    {D : Type*}
    {R : Type*} [OrderedAddCommGroup R]
    {f: D → R}
    {C: Set D}
    (min: MinimumOn f C)
    :
    MaximumOn (fun x: D => -(f x)) C
    := by
        constructor
        case value => exact -min.value
        case yIsInImage =>
            let ⟨xmin, hx⟩ := min.yIsInImage
            use xmin
            rw [neg_inj]
            exact hx
        case isMax =>
            intro x
            intro xInC
            exact min.isMin x xInC |> neg_le_neg

/-- max_x f(x) = -min_x (-f(x)) -/
def max_obj_to_neg_min_neg_obj
    {D : Type*}
    {R : Type*} [OrderedAddCommGroup R]
    {f: D → R}
    {C: Set D}
    (max: MaximumOn f C)
    :
    MinimumOn (fun x: D => -(f x)) C
    := by
        constructor
        case value => exact -max.value
        case yIsInImage =>
            let ⟨xmax, hx⟩ := max.yIsInImage
            use xmax
            rw [neg_inj]
            exact hx
        case isMin =>
            intro x
            intro xInC
            exact max.isMax x xInC |> neg_le_neg

/-- y s.t. f(y) = min of f(x) for all x in C -/
def ArgumentMinimumOn
    {Domain: Type*}
    {Range: Type*} [Preorder Range]
    (objective: Domain → Range)
    (ConstraintSet: Set Domain)
    : Set Domain
    := setOf fun xmin: Domain =>
        xmin ∈ ConstraintSet
        ∧ ∀ x ∈ ConstraintSet, objective xmin ≤ objective x

/-- inf of f(x) for all x in C -/
structure InfimumOn
    {Domain: Type*}
    {Range: Type*} [Preorder Range]
    (objective: Domain → Range)
    (ConstraintSet: Set Domain)
    where
    value : Range
    isLeAll : ∀ x ∈ ConstraintSet, value ≤ objective x
    isLargestLeAll:
        ∀ y : Range, (∀ x ∈ ConstraintSet, y ≤ objective x) -> y ≤ value

/-- sup of f(x) for all x in C -/
structure SupremumOn
    {Domain: Type*}
    {Range: Type*} [Preorder Range]
    (objective: Domain → Range)
    (ConstraintSet: Set Domain)
    where
    value : Range
    isGeAll : (∀ x ∈ ConstraintSet, objective x ≤ value)
    isSmallestGeAll:
        ∀ y : Range, (∀ x ∈ ConstraintSet, objective x ≤ y) → value ≤ y

/- Remark -/
/-- inf_x f(x) = -sup_x (-f(x)) -/
def inf_obj_to_neg_sup_neg_obj
    {D : Type*}
    {R : Type*} [OrderedAddCommGroup R]
    {f: D → R}
    {C: Set D}
    (inf: InfimumOn f C)
    :
    SupremumOn (fun x: D => -(f x)) C
    := by
        constructor
        case value => exact -inf.value
        case isGeAll =>
            intro x
            intro xInC
            show -f x ≤ -inf.value
            exact inf.isLeAll x xInC |> neg_le_neg
        case isSmallestGeAll =>
            intro y
            intro yIsGeNegAll
            have negYIsLeAll := fun x : D => fun xInC: x ∈ C =>
                yIsGeNegAll x xInC |> neg_le.mp
            exact inf.isLargestLeAll (-y) negYIsLeAll |> neg_le.mp

/--
If a function is L-continuous, any two points that are a distance `d` apart
are no more than `L * d` apart when mapped through the function.
-/
structure LipschitzContinuous
    [Field ℝ] [Lattice ℝ]
    {ℝn : Type*} [NormedAddCommGroup ℝn] [NormedSpace ℝ ℝn]
    (f : ℝn → ℝ)
    where
    L : NNReal
    h : ∀ x y : ℝn, abs ((f y) - (f x)) ≤ L * dist y x


def Vec
    (E : Type u)
    (n : Nat)
    : Type u
    := Fin n → E

-- theorem holder_inequality
--     (D : Type*) [AddCommGroup D]
--     (p : ENNReal)
--     (pnz : p ≥ 1)
--     (q : ENNReal)
--     (qnz : q ≥ 1)
--     (invAddEq : 1/p + 1/q = 1)
--     (x : lp D p)
--     (y : lp D q)
--     : norm (x * y) ≤ ‖x‖ * ‖y‖
--     := sorry

theorem holder_inequality
    (D : Type*) [AddCommGroup D]
    (p q: ENNReal)
    (pnz : p ≥ 1)
    (qnz : q ≥ 1)
    (invAddEq : p.IsConjExponent q)
    (x : lp D p)
    (y : lp D q)
    : norm (x * y) ≤ ‖x‖ * ‖y‖
    := sorry


#eval ![1, 2] + ![3, 4]  -- ![4, 6]
#check ![1, 2]
