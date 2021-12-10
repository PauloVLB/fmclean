lemma succ_mul (a b : mynat) : succ a * b = a * b + b :=
begin
induction b with h hd,
rw mul_zero,
rw mul_zero,
rw add_zero,
refl,
rw mul_succ,
rw mul_succ,
rw hd,
rw add_succ,
rw add_succ,
rw add_right_comm,
refl,

end