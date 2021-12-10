theorem add_le_add_left {a b : mynat} (h : a ≤ b) (t : mynat) :
  t + a ≤ t + b :=
begin
rw add_comm,
rw add_comm t b,
revert t,
exact add_le_add_right h,
end