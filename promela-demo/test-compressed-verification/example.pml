/*
Example code that would explore 2^32(4 billion) states.
*/
int val;
inline check() {
	if
	:: (val == -1196372740) || (val == -222966779) || (val == -233545464)
		 -> c_code { printf("assertion violated %d\n", now.val); }
	:: else /* no match */
	fi
}
active [8] proctype word()
{ /* _pid = 0..7 -- each proc owns 4 bits */
end: do
:: d_step { val = val | 1 << ((4 * _pid) + 0); check() }
:: d_step { val = val | 1 << ((4 * _pid) + 1); check() }
:: d_step { val = val | 1 << ((4 * _pid) + 2); check() }
:: d_step { val = val | 1 << ((4 * _pid) + 3); check() }
od
}
