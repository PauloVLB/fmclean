lemma add_right_eq_zero {a b : mynat} : a + b = 0 → a = 0 :=
begin
intro h,
rw add_comm at h,
exact add_left_eq_zero h,
end