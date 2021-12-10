theorem mul_pos (a b : mynat) : a ≠ 0 → b ≠ 0 → a * b ≠ 0 :=
begin
intros f h g,
cases b with n,
apply h,
rw mul_zero at g,
exact g,
rw mul_succ at g,
have gg := add_left_eq_zero g,
apply f,
exact gg,
end