theorem mul_eq_zero_iff (a b : mynat): a * b = 0 ↔ a = 0 ∨ b = 0 :=
begin
split,
exact eq_zero_or_eq_zero_of_mul_eq_zero _ _,
intro h,
cases h with ha hb,
rw ha,
rw zero_mul,
refl,
rw hb,
rw mul_zero,
refl,

end