import Mathlib.Order.Bounds.Basic
import Mathlib.Algebra.Order.Group.Basic
import Mathlib.Algebra.Group.Defs

-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Order/Group/Defs.html#neg_le_neg

/-!

Math implementation for lecture 00:
https://github.com/stephenbeckr/convex-optimization-class/blob/main/Notes/00_IntroToOptProblems.pdf

uses CvxLean as a reference:
- https://github.com/verified-optimization/CvxLean/blob/c62c2f292c6420f31a12e738ebebdfed50f6f840/CvxLean/Lib/Minimization.lean

-/


/- Minimization -/
structure MinimumOn
    {Domain: Type u}
    {Range: Type u} [Preorder Range]
    (objective: Domain → Range)
    (ConstraintSet: Set Domain)
    where
    value : Range
    yIsInImage : ∃ x ∈ ConstraintSet, objective x = value
    isMin: ∀ x ∈ ConstraintSet, value ≤ objective x

/- Maximization -/
structure MaximumOn
    {Domain: Type u}
    {Range: Type u} [Preorder Range]
    (objective: Domain → Range)
    (ConstraintSet: Set Domain)
    where
    value : Range
    yIsInImage : ∃ x ∈ ConstraintSet, objective x = value
    isMax: ∀ x ∈ ConstraintSet, objective x ≤ value

/- Remark -/
/-- min_x f(x) = -max_x (-f(x)) -/
def min_obj_to_neg_max_neg_obj
    {D R : Type} [OrderedAddCommGroup R]
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
            have minLeX := min.isMin x xInC
            exact neg_le_neg minLeX

/-- max_x f(x) = -min_x (-f(x)) -/
def max_obj_to_neg_min_neg_obj
    {D R : Type} [OrderedAddCommGroup R]
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
            have maxGeX := max.isMax x xInC
            exact neg_le_neg maxGeX
