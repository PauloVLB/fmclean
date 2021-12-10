theorem add_right_cancel_iff (t a b : mynat) :  a + t = b + t ↔ a = b :=
begin
split,
exact add_right_cancel a t b,
intro h,
rw h,
refl,

end