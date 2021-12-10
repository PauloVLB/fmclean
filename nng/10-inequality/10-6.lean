theorem le_antisymm (a b : mynat) (hab : a ≤ b) (hba : b ≤ a) : a = b :=
begin
cases hab with c hc,
cases hba with d hd,
rw hd at hc,
rw add_assoc at hc,
symmetry at hc,
have dc := eq_zero_of_add_right_eq_self hc,
have dz := add_right_eq_zero dc,
rw hd,
rw dz,
refl,


end