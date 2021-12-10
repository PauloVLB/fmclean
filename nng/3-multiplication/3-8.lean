lemma mul_comm (a b : mynat) : a * b = b * a :=
begin
induction b with h hd,
rw zero_mul,
rw mul_zero,
refl,
rw mul_succ,
rw succ_mul,
rw hd,
simp,

end