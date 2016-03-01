Require Import Frap.

Theorem another_important_theorem : length [1; 2; 3] = 1 + length [4; 5].
Proof.
  simplify.
  equality.
Qed.

Theorem length_concat : forall A (xs ys : list A), length (xs ++ ys) = length xs + length ys.
Proof.
  induct xs.
  induct ys.
  simplify.
  equality.

  simplify.
  equality.

  simplify.
  f_equal.
  rewrite IHxs.
  equality.
Qed.

Theorem length_rev : forall A (xs : list A), length xs = length (rev xs).
Proof.
  induct xs.
  simplify.
  equality.
  simplify.
  rewrite length_concat.
  simplify.
  linear_arithmetic.
Qed.