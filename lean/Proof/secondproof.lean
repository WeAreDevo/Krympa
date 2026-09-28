import Mathlib.Tactic.NthRewrite

class Magma (α : Type _) where
  op : α → α → α

infix:65 " ◇ " => Magma.op

theorem Equation947_implies_Equation3897 (G : Type _) [Magma G]
      (op_law : ∀ x y z : G, x = y ◇ ((z ◇ x) ◇ (y ◇ x))) :
    ∀ x y z : G, x ◇ x = (y ◇ (z ◇ x)) ◇ x :=
  have lemma_1 (x y z w : G) :
      ((x ◇ y) ◇ (z ◇ y)) = (w ◇ (y ◇ (w ◇ ((x ◇ y) ◇ (z ◇ y))))) := by
    nth_rw 3 [op_law y z x]
    exact op_law ((x ◇ y) ◇ (z ◇ y)) w z

  have lemma_2 (x y z : G) :
      ((x ◇ y) ◇ (z ◇ y)) = (z ◇ (y ◇ y)) := by
    nth_rw 4 [op_law y z x]
    exact lemma_1 x y z z

  have lemma_3 (x y : G) :
      y = x ◇ (x ◇ (y ◇ y)) := by
    nth_rw 1 [←lemma_2 x y x]
    exact op_law y x x

  have lemma_4 (x y z : G) :
      (x ◇ x) = ((y ◇ (z ◇ x)) ◇ x) := by
    calc
      (x ◇ x) = ((y ◇ (z ◇ x)) ◇ ((y ◇ (z ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x)))) := by
        nth_rw 1 [←lemma_3]
      _ = ((y ◇ (z ◇ x)) ◇ ((y ◇ (z ◇ x)) ◇
              (z ◇ (z ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))))))) := by
        nth_rw 2 [←lemma_3]
      _ = ((y ◇ (z ◇ x)) ◇ ((y ◇ (z ◇ x)) ◇ (z ◇ (z ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))))))) := by
        nth_rw 1 [lemma_2]
      _ = ((y ◇ (z ◇ x)) ◇ ((y ◇ (z ◇ x)) ◇ (z ◇ (z ◇ x)))) := by
        nth_rw 1 [←lemma_3]
      _ = ((y ◇ (z ◇ x)) ◇ (z ◇ ((z ◇ x) ◇ (z ◇ x)))) := by
        nth_rw 1 [lemma_2]
      _ = ((y ◇ (z ◇ x)) ◇ (z ◇ (z ◇ (x ◇ x)))) := by
        nth_rw 1 [lemma_2]
      _ = ((y ◇ (z ◇ x)) ◇ x) := by
        nth_rw 1 [←lemma_3]

  show _ by
    exact lemma_4
