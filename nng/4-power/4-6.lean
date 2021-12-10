lemma mul_pow (a b n : mynat) : (a * b) ^ n = a ^ n * b ^ n :=
begin
induction n with h hd,
rw pow_zero,
rw pow_zero,
rw pow_zero,
rw mul_one,
refl,
rw pow_succ,
rw hd,
rw pow_succ,
rw pow_succ,
simp,

end